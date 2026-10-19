/**
 * Tests for the off-chain sparse Merkle tree (src/k17/smt.ts) and the
 * member / admission / removal message helpers (src/k17/attest.ts).
 * Roots are checked against an independent naive recomputation, and each
 * signed message is checked against literal domain bytes and verified with
 * the same RabinVerifier the contract uses.
 */
import { expect } from 'chai'
import { createHash } from 'crypto'
import { RabinVerifier, RabinSig } from 'scrypt-ts-lib'
import { toByteString } from 'scrypt-ts'
import {
    TREE_DEPTH,
    EMPTY_LEAF,
    EMPTY_HASHES,
    LEAF_DOMAIN,
    encodeLeafPre,
    decodeLeafPre,
    leafHashOf,
    SparseMerkleTree,
} from '../src/k17/smt'
import {
    newAttester,
    keyHash,
    MEMBER_DOMAIN,
    ADMIT_DOMAIN,
    REMOVE_DOMAIN,
    memberMessage,
    signMemberReading,
    admitMessage,
    signAdmission,
    removeMessage,
    signRemoval,
} from '../src/k17/attest'
import { encodeCell } from '../src/k17/isa'

/** sha256 of a hex string, returned as hex. */
function sha(hex: string): string {
    return createHash('sha256').update(Buffer.from(hex, 'hex')).digest('hex')
}

/**
 * Independent root computation: fold the leaf hash up 16 levels using the
 * sibling list, without sharing code with SparseMerkleTree.
 */
function naiveRoot(
    leafHash: string,
    siblings: string[],
    index: number
): string {
    let node = leafHash
    for (let level = 0; level < 16; level++) {
        node =
            (index >> level) & 1
                ? sha(siblings[level] + node)
                : sha(node + siblings[level])
    }
    return node
}

const KEY_HASH = '11'.repeat(32)
const PAYOUT = '22'.repeat(20)

describe('K17 sparse Merkle tree', function () {
    it('has the specified constants', () => {
        expect(TREE_DEPTH).to.equal(16)
        expect(EMPTY_LEAF).to.equal('00'.repeat(32))
        expect(LEAF_DOMAIN).to.equal('4b31374c')
        expect(EMPTY_HASHES.length).to.equal(17)
        expect(EMPTY_HASHES[0]).to.equal(EMPTY_LEAF)
        expect(EMPTY_HASHES[1]).to.equal(sha('00'.repeat(64)))
    })

    it('empty tree root equals the hand-computed chain', () => {
        let node = '00'.repeat(32)
        for (let level = 0; level < 16; level++) node = sha(node + node)
        expect(EMPTY_HASHES[16]).to.equal(node)
        expect(new SparseMerkleTree().root()).to.equal(node)
    })

    it('encodes and decodes the leaf preimage', () => {
        const pre = encodeLeafPre(KEY_HASH, PAYOUT, 7n, 3n)
        expect(pre.length).to.equal(120)
        expect(pre).to.equal(
            KEY_HASH + PAYOUT + encodeCell(7n) + encodeCell(3n)
        )
        expect(decodeLeafPre(pre)).to.deep.equal({
            keyHashHex: KEY_HASH,
            payoutHex: PAYOUT,
            lastRound: 7n,
            flags: 3n,
        })
        expect(encodeLeafPre(KEY_HASH, PAYOUT, 7n)).to.equal(
            KEY_HASH + PAYOUT + encodeCell(7n) + encodeCell(0n)
        )
    })

    it('hashes leaves with the K17L domain; empty preimage is EMPTY_LEAF', () => {
        const pre = encodeLeafPre(KEY_HASH, PAYOUT, 1n)
        expect(leafHashOf(pre)).to.equal(sha('4b31374c' + pre))
        expect(leafHashOf('')).to.equal(EMPTY_LEAF)
    })

    it('a single leaf at index 5 gives the hand-computed root', () => {
        const pre = encodeLeafPre(KEY_HASH, PAYOUT, 9n)
        const tree = new SparseMerkleTree()
        tree.set(5, pre)
        const expected = naiveRoot(
            sha('4b31374c' + pre),
            EMPTY_HASHES.slice(0, 16),
            5
        )
        expect(tree.root()).to.equal(expected)
        expect(tree.get(5)).to.equal(pre)
        expect(tree.get(6)).to.equal(undefined)
    })

    it('proof verifies at its index only and rejects tampering', () => {
        const pre = encodeLeafPre(KEY_HASH, PAYOUT, 9n)
        const tree = new SparseMerkleTree()
        tree.set(5, pre)
        tree.set(40000, encodeLeafPre('33'.repeat(32), PAYOUT, 2n))
        const p = tree.proof(5)
        expect(p.proof.length).to.equal(1024)
        expect(p.leafPre).to.equal(pre)
        expect(p.leafIndex).to.equal(5n)
        const root = tree.root()
        expect(SparseMerkleTree.verify(root, pre, p.proof, 5n)).to.equal(true)
        expect(SparseMerkleTree.verify(root, pre, p.proof, 6n)).to.equal(false)
        const flipped = 'ff' + pre.slice(2)
        expect(SparseMerkleTree.verify(root, flipped, p.proof, 5n)).to.equal(
            false
        )
        const badProof = 'ff' + p.proof.slice(2)
        expect(SparseMerkleTree.verify(root, pre, badProof, 5n)).to.equal(false)
        // an empty slot proves as EMPTY_LEAF
        const q = tree.proof(77)
        expect(q.leafPre).to.equal('')
        expect(SparseMerkleTree.verify(root, '', q.proof, 77n)).to.equal(true)
    })

    it('rootAfter equals the root of a tree with the change applied', () => {
        const tree = new SparseMerkleTree()
        tree.set(5, encodeLeafPre(KEY_HASH, PAYOUT, 9n))
        tree.set(6, encodeLeafPre('44'.repeat(32), PAYOUT, 1n))
        const p = tree.proof(5)
        const changed = encodeLeafPre(KEY_HASH, PAYOUT, 10n)
        const predicted = SparseMerkleTree.rootAfter(changed, p.proof, 5n)
        tree.set(5, changed)
        expect(predicted).to.equal(tree.root())
        // removal: rootAfter of '' equals the root after clearing
        const p2 = tree.proof(5)
        const afterRemove = SparseMerkleTree.rootAfter('', p2.proof, 5n)
        tree.set(5, '')
        expect(afterRemove).to.equal(tree.root())
        expect(tree.get(5)).to.equal(undefined)
    })

    it('constructor leaves match incremental sets; clearing all restores empty', () => {
        const a = encodeLeafPre(KEY_HASH, PAYOUT, 1n)
        const b = encodeLeafPre('55'.repeat(32), PAYOUT, 2n)
        const built = new SparseMerkleTree(
            new Map([
                [0, a],
                [65535, b],
            ])
        )
        const incremental = new SparseMerkleTree()
        incremental.set(0, a)
        incremental.set(65535, b)
        expect(built.root()).to.equal(incremental.root())
        incremental.set(0, '')
        incremental.set(65535, '')
        expect(incremental.root()).to.equal(EMPTY_HASHES[16])
    })

    it('rejects out-of-range indexes and malformed leaves', () => {
        const tree = new SparseMerkleTree()
        expect(() => tree.set(65536, '')).to.throw()
        expect(() => tree.set(-1, '')).to.throw()
        expect(() => tree.proof(65536)).to.throw()
        expect(() => tree.set(1, 'abcd')).to.throw()
        expect(() => encodeLeafPre('11', PAYOUT, 1n)).to.throw()
    })
})

describe('K17 member / admission / removal messages', function () {
    this.timeout(120_000)
    const ID = '9a'.repeat(32)
    const attester = newAttester(Buffer.alloc(32, 31))
    const sponsor = newAttester(Buffer.alloc(32, 32))
    const newcomer = newAttester(Buffer.alloc(32, 33))

    /** Verify a signature over a message hex with the contract's verifier. */
    function ok(message: string, sig: RabinSig, pub: bigint): boolean {
        return RabinVerifier.verifySig(toByteString(message), sig, pub)
    }

    it('has the specified domain constants', () => {
        expect(MEMBER_DOMAIN).to.equal('4b313754')
        expect(ADMIT_DOMAIN).to.equal('4b313744')
        expect(REMOVE_DOMAIN).to.equal('4b313758')
    })

    it('member attestation layout and signature', () => {
        const message = memberMessage(ID, 5n, 77n)
        expect(message).to.equal(
            '4b313754' + ID + encodeCell(5n) + encodeCell(77n)
        )
        const sig = signMemberReading(attester, ID, 5n, 77n)
        expect(ok(message, sig, attester.pub)).to.equal(true)
        expect(ok(memberMessage(ID, 5n, 78n), sig, attester.pub)).to.equal(
            false
        )
        expect(ok(message, sig, sponsor.pub)).to.equal(false)
    })

    it('admission layout and signature', () => {
        const message = admitMessage(ID, 5n, 2n, 300n, newcomer.pub, PAYOUT)
        expect(message).to.equal(
            '4b313744' +
                ID +
                encodeCell(5n) +
                encodeCell(2n) +
                encodeCell(300n) +
                keyHash(newcomer.pub) +
                PAYOUT
        )
        const sig = signAdmission(
            sponsor,
            ID,
            5n,
            2n,
            300n,
            newcomer.pub,
            PAYOUT
        )
        expect(ok(message, sig, sponsor.pub)).to.equal(true)
        // bound to the leaf index
        expect(
            ok(
                admitMessage(ID, 5n, 2n, 301n, newcomer.pub, PAYOUT),
                sig,
                sponsor.pub
            )
        ).to.equal(false)
        // bound to the payout
        expect(
            ok(
                admitMessage(ID, 5n, 2n, 300n, newcomer.pub, '33'.repeat(20)),
                sig,
                sponsor.pub
            )
        ).to.equal(false)
    })

    it('removal layout and signature', () => {
        const leafHash = leafHashOf(encodeLeafPre(KEY_HASH, PAYOUT, 4n))
        const message = removeMessage(ID, 5n, 2n, 300n, leafHash)
        expect(message).to.equal(
            '4b313758' +
                ID +
                encodeCell(5n) +
                encodeCell(2n) +
                encodeCell(300n) +
                leafHash
        )
        const sig = signRemoval(sponsor, ID, 5n, 2n, 300n, leafHash)
        expect(ok(message, sig, sponsor.pub)).to.equal(true)
        expect(
            ok(removeMessage(ID, 5n, 3n, 300n, leafHash), sig, sponsor.pub)
        ).to.equal(false)
    })

    it('the three domains never collide for the same field values', () => {
        const a = memberMessage(ID, 1n, 1n).slice(0, 8)
        const b = admitMessage(ID, 1n, 1n, 1n, newcomer.pub, PAYOUT).slice(0, 8)
        const c = removeMessage(ID, 1n, 1n, 1n, EMPTY_LEAF).slice(0, 8)
        expect(new Set([a, b, c]).size).to.equal(3)
    })
})
