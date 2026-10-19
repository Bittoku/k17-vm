/**
 * Off-chain sparse Merkle tree for the K17+ roster machine.
 *
 * The tree has TREE_DEPTH = 16 levels (65 536 leaves) and hashes with
 * SHA-256. A node is sha256(left || right). A leaf hash is
 * sha256(LEAF_DOMAIN || leafPre), where leafPre is the 60-byte member record
 * keyHash(32) || payout(20) || cell(lastRound) || cell(flags). An empty leaf
 * has leafPre '' and hash EMPTY_LEAF (32 zero bytes). EMPTY_HASHES holds the
 * root of an all-empty subtree at each height.
 *
 * A proof is the 16 sibling hashes concatenated, level 0 (the leaf's own
 * sibling) first. At level k, bit k of the leaf index tells whether the
 * current node is the right child (1) or the left child (0).
 *
 * All values are lowercase hex strings. This module is the reference the
 * on-chain tree instructions must reproduce.
 */

import { createHash } from 'crypto'
import { CELL, decodeCell, encodeCell } from './isa'

/** Number of tree levels; the tree holds 2^TREE_DEPTH leaves. */
export const TREE_DEPTH = 16

/** Hash of an empty leaf: 32 zero bytes. */
export const EMPTY_LEAF = '00'.repeat(32)

/** Domain prefix of a leaf hash, ASCII "K17L". */
export const LEAF_DOMAIN = '4b31374c'

/** Hex length of a SHA-256 hash. */
const HASH_HEX = 64

/** Hex length of a leaf preimage: 32 + 20 + 4 + 4 bytes. */
const LEAF_PRE_HEX = 120

/**
 * SHA-256 of a hex string. Input: hex. Output: hex digest.
 */
function sha256Hex(hex: string): string {
    return createHash('sha256').update(Buffer.from(hex, 'hex')).digest('hex')
}

/**
 * Root hash of an all-empty subtree for each height 0..TREE_DEPTH.
 * EMPTY_HASHES[0] = EMPTY_LEAF; EMPTY_HASHES[k+1] = sha256(h || h).
 */
export const EMPTY_HASHES: string[] = (() => {
    const hashes = [EMPTY_LEAF]
    for (let level = 0; level < TREE_DEPTH; level++) {
        const below = hashes[level]
        hashes.push(sha256Hex(below + below))
    }
    return hashes
})()

/**
 * Build a leaf preimage.
 * Input: 32-byte key hash hex, 20-byte payout hex, last round, flags
 * (default 0). Output: 120 hex chars. Throws on wrong lengths or a cell
 * out of range.
 */
export function encodeLeafPre(
    keyHashHex: string,
    payoutHex: string,
    lastRound: bigint,
    flags: bigint = 0n
): string {
    if (!/^[0-9a-f]{64}$/.test(keyHashHex)) {
        throw new Error('key hash must be 32 bytes of lowercase hex')
    }
    if (!/^[0-9a-f]{40}$/.test(payoutHex)) {
        throw new Error('payout must be 20 bytes of lowercase hex')
    }
    return keyHashHex + payoutHex + encodeCell(lastRound) + encodeCell(flags)
}

/**
 * Split a leaf preimage into its fields.
 * Input: 120-hex-char preimage. Output: key hash hex, payout hex, lastRound,
 * flags. Throws on a wrong length.
 */
export function decodeLeafPre(leafPreHex: string): {
    keyHashHex: string
    payoutHex: string
    lastRound: bigint
    flags: bigint
} {
    if (leafPreHex.length !== LEAF_PRE_HEX) {
        throw new Error('leaf preimage must be ' + LEAF_PRE_HEX + ' hex chars')
    }
    const cellHex = CELL * 2
    return {
        keyHashHex: leafPreHex.slice(0, 64),
        payoutHex: leafPreHex.slice(64, 104),
        lastRound: decodeCell(leafPreHex.slice(104, 104 + cellHex)),
        flags: decodeCell(leafPreHex.slice(104 + cellHex)),
    }
}

/**
 * Hash a leaf preimage.
 * Input: leaf preimage hex, or '' for an empty leaf. Output: 64-hex-char
 * leaf hash: sha256(LEAF_DOMAIN || pre), or EMPTY_LEAF for ''.
 */
export function leafHashOf(leafPreHex: string): string {
    return leafPreHex === '' ? EMPTY_LEAF : sha256Hex(LEAF_DOMAIN + leafPreHex)
}

/** Throw unless `index` is an integer leaf position in [0, 2^TREE_DEPTH). */
function checkIndex(index: number | bigint): void {
    if (typeof index === 'number' && !Number.isInteger(index)) {
        throw new Error('leaf index must be an integer: ' + index)
    }
    if (index < 0 || index >= 2 ** TREE_DEPTH) {
        throw new Error('leaf index out of range: ' + index)
    }
}

/** Throw unless `leafPreHex` is '' or a well-formed preimage. */
function checkLeafPre(leafPreHex: string): void {
    if (leafPreHex !== '' && !/^[0-9a-f]{120}$/.test(leafPreHex)) {
        throw new Error('leaf preimage must be empty or 120 hex chars')
    }
}

/**
 * Fold a leaf hash up the tree along a proof.
 * Input: leaf hash hex, proof (16 siblings, level 0 first), leaf index.
 * Output: the root hex.
 */
function foldRoot(
    leafHash: string,
    proofHex: string,
    leafIndex: bigint
): string {
    if (proofHex.length !== TREE_DEPTH * HASH_HEX) {
        throw new Error('proof must be ' + TREE_DEPTH * HASH_HEX + ' hex chars')
    }
    checkIndex(leafIndex)
    let node = leafHash
    for (let level = 0; level < TREE_DEPTH; level++) {
        const sibling = proofHex.slice(level * HASH_HEX, (level + 1) * HASH_HEX)
        node =
            (leafIndex >> BigInt(level)) & 1n
                ? sha256Hex(sibling + node)
                : sha256Hex(node + sibling)
    }
    return node
}

/**
 * Sparse Merkle tree over 2^16 leaves. Only non-empty leaves are stored;
 * empty subtrees use EMPTY_HASHES. Internal nodes are cached by
 * "level:position" and updated along one path per set().
 */
export class SparseMerkleTree {
    private readonly leaves = new Map<number, string>()
    private readonly nodes = new Map<string, string>()

    /**
     * Input: optional map from leaf index to leaf preimage hex. Empty
     * preimages are ignored.
     */
    constructor(leaves?: Map<number, string>) {
        if (leaves) {
            for (const [index, pre] of leaves) this.set(index, pre)
        }
    }

    /** Output: the current root hex. */
    root(): string {
        return this.node(TREE_DEPTH, 0)
    }

    /**
     * Input: leaf index. Output: the stored preimage, or undefined if the
     * leaf is empty.
     */
    get(index: number): string | undefined {
        checkIndex(index)
        return this.leaves.get(index)
    }

    /**
     * Write a leaf and refresh the hashes on its path.
     * Input: leaf index, preimage hex or '' to clear. Output: none. Throws
     * on a bad index or a malformed preimage.
     */
    set(index: number, leafPreHex: string): void {
        checkIndex(index)
        checkLeafPre(leafPreHex)
        if (leafPreHex === '') this.leaves.delete(index)
        else this.leaves.set(index, leafPreHex)
        let position = index
        this.nodes.set('0:' + position, leafHashOf(leafPreHex))
        for (let level = 1; level <= TREE_DEPTH; level++) {
            position >>= 1
            this.nodes.set(
                level + ':' + position,
                sha256Hex(
                    this.node(level - 1, position * 2) +
                        this.node(level - 1, position * 2 + 1)
                )
            )
        }
    }

    /**
     * Membership (or emptiness) proof for one leaf.
     * Input: leaf index. Output: the leaf preimage ('' if empty), the 16
     * siblings concatenated (1024 hex chars, level 0 first), and the index.
     */
    proof(index: number): {
        leafPre: string
        proof: string
        leafIndex: bigint
    } {
        checkIndex(index)
        let siblings = ''
        for (let level = 0; level < TREE_DEPTH; level++) {
            siblings += this.node(level, (index >> level) ^ 1)
        }
        return {
            leafPre: this.leaves.get(index) ?? '',
            proof: siblings,
            leafIndex: BigInt(index),
        }
    }

    /**
     * Check a proof against a root.
     * Input: root hex, leaf preimage ('' for empty), proof hex, leaf index.
     * Output: true if the proof folds to the root. A malformed proof length
     * or index yields false.
     */
    static verify(
        rootHex: string,
        leafPreHex: string,
        proofHex: string,
        leafIndex: bigint
    ): boolean {
        try {
            return (
                foldRoot(leafHashOf(leafPreHex), proofHex, leafIndex) ===
                rootHex
            )
        } catch {
            return false
        }
    }

    /**
     * Root after replacing one leaf, computed from its proof alone.
     * Input: new leaf preimage ('' to clear), proof of the old leaf, index.
     * Output: the new root hex. Throws on a malformed proof or index.
     */
    static rootAfter(
        leafPreHex: string,
        proofHex: string,
        leafIndex: bigint
    ): string {
        checkLeafPre(leafPreHex)
        return foldRoot(leafHashOf(leafPreHex), proofHex, leafIndex)
    }

    /** Node hash at (level, position); empty subtrees default. */
    private node(level: number, position: number): string {
        return this.nodes.get(level + ':' + position) ?? EMPTY_HASHES[level]
    }
}
