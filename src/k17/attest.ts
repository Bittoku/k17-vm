/**
 * Attestation helpers for the SIGVERIFY instruction (K17+).
 *
 * An attester (a sensor node, an oracle, a roster member) holds a Rabin
 * private key. It signs `attestMessage(tag, value)` and hands the signature
 * to whichever keeper relays the reading on chain. The contract verifies the
 * signature with `RabinVerifier.verifySig` from scrypt-ts-lib against the
 * roster public key named by the SIGVERIFY operand.
 *
 * Rabin is used rather than ECDSA because Bitcoin script can only check an
 * ECDSA signature over the transaction digest (OP_CHECKSIG), never over an
 * arbitrary message, while a Rabin signature is checked with one modular
 * multiplication over big integers, which BSV script has natively.
 *
 * Security level 6 (3072-bit modulus) is the scrypt-ts-lib default and must
 * match on both sides; it is fixed here.
 */

import { Rabin, RabinPrivateKey, toRabinSig } from 'rabinsig'
import { RabinPubKey, RabinSig } from 'scrypt-ts-lib'
import { bsv } from 'scrypt-ts'
import { createHash } from 'crypto'
import { attestMessage, encodeCell, ENDORSE_DOMAIN } from './isa'

/** Security level shared with RabinVerifier.SECURITY_LEVEL. */
export const RABIN_SECURITY_LEVEL = 6

const rabin = new Rabin(RABIN_SECURITY_LEVEL)

/**
 * Put a Rabin signature in its canonical form (v3.1).
 * Purpose: the verifier checks s^2 mod n, so s, n - s, -s and s + k*n all
 * verify the same message. Nobody signs the unlocking script, so a relayer
 * could swap one form for another and change the txid; the contract
 * therefore accepts only 0 < s < n/2. Every sign* helper here returns that
 * form, and planCycle normalises any signature it is given.
 * Input: a signature (any representative of s) and the public modulus n it
 * verifies under. Output: the same signature with s replaced by
 * min(s mod n, n - s mod n); the padding is unchanged. NO_SIG (s = 0) is
 * returned unchanged. Throws when n is not positive.
 */
export function canonicalSig(sig: RabinSig, pub: RabinPubKey): RabinSig {
    if (pub <= 0n) throw new Error('Rabin public key must be positive')
    if (sig.s === 0n) return sig
    const reduced = ((sig.s % pub) + pub) % pub
    const s = 2n * reduced < pub ? reduced : pub - reduced
    return { s, padding: sig.padding }
}

/** Private key plus its public modulus. */
export interface Attester {
    priv: RabinPrivateKey
    pub: RabinPubKey
}

/**
 * Generate an attester keypair. Input: optional 32-byte seed for
 * deterministic tests. Output: private key and public modulus.
 */
export function newAttester(seed?: Buffer): Attester {
    const priv = seed
        ? rabin.generatePrivKeyFromSeed(seed)
        : rabin.generatePrivKey()
    return { priv, pub: rabin.privKeyToPubKey(priv) }
}

/**
 * Sign a reading for `TAG VAL SIGVERIFY k`.
 * Input: attester, tag (replay guard), value (reading). Output: signature in
 * the shape the contract and the reference VM consume.
 */
export function signReading(
    attester: Attester,
    tag: bigint,
    value: bigint
): RabinSig {
    return canonicalSig(
        toRabinSig(rabin.sign(attestMessage(tag, value), attester.priv)),
        attester.pub
    )
}

/**
 * Domain prefix of an ATTEST message, ASCII "K17M" (memory roster). Kept
 * apart from ATTEST_DOMAIN ("K17A", SIGVERIFY) so that a SIGVERIFY
 * signature can never be presented to ATTEST or the other way round.
 */
export const ATTEST_DOMAIN_M = '4b31374d'

/**
 * Message an attester signs for `TAG VAL SLOT ATTEST` on one machine.
 * Input: the machine's 32-byte instance id (64 hex chars), tag, value.
 * Output: hex of ATTEST_DOMAIN_M + instanceId + cell(tag) + cell(value).
 * The instance id stops a reading signed for one machine being replayed
 * into another machine that shares the roster key.
 */
export function attestMessageFor(
    instanceIdHex: string,
    tag: bigint,
    value: bigint
): string {
    return ATTEST_DOMAIN_M + instanceIdHex + encodeCell(tag) + encodeCell(value)
}

/**
 * Sign a reading for `TAG VAL SLOT ATTEST` on one machine.
 * Input: attester, the machine's instance id hex, tag, value.
 * Output: Rabin signature over attestMessageFor.
 */
export function signReadingFor(
    attester: Attester,
    instanceIdHex: string,
    tag: bigint,
    value: bigint
): RabinSig {
    return canonicalSig(
        toRabinSig(
            rabin.sign(
                attestMessageFor(instanceIdHex, tag, value),
                attester.priv
            )
        ),
        attester.pub
    )
}

/** The empty signature a keeper passes when the cycle has no SIGVERIFY. */
export const NO_SIG: RabinSig = { s: 0n, padding: '' }

/** Fixed width of an encoded roster public key: 3072 bits. */
export const KEY_BYTES = 384

/**
 * Encode a Rabin public modulus as the roster byte string.
 * Input: public key. Output: 768 hex characters, little-endian unsigned,
 * zero-padded (the form Utils.fromLEUnsigned reads on chain). Throws if the
 * key needs more than KEY_BYTES bytes.
 */
export function pubKeyBytes(pub: RabinPubKey): string {
    let hex = pub.toString(16)
    if (hex.length % 2) hex = '0' + hex
    const bigEndian = Buffer.from(hex, 'hex')
    if (pub < 0n || bigEndian.length > KEY_BYTES) {
        throw new Error('public key does not fit in ' + KEY_BYTES + ' bytes')
    }
    const out = Buffer.alloc(KEY_BYTES)
    bigEndian.reverse().copy(out)
    return out.toString('hex')
}

/**
 * Decode a roster byte string back to a public modulus.
 * Input: hex from pubKeyBytes. Output: the bigint public key.
 */
export function pubKeyFromBytes(hex: string): RabinPubKey {
    const bigEndian = Buffer.from(hex, 'hex').reverse()
    return BigInt('0x' + (bigEndian.toString('hex') || '0'))
}

/**
 * Hash of a roster key as stored in the roster and in endorsements.
 * Input: public key. Output: hex of sha256(pubKeyBytes(pub)).
 */
export function keyHash(pub: RabinPubKey): string {
    return createHash('sha256')
        .update(Buffer.from(pubKeyBytes(pub), 'hex'))
        .digest('hex')
}

/**
 * Message a roster member signs to endorse a new member into a slot.
 * Input: the machine's 32-byte instance id (64 hex chars), tag (replay
 * guard), new member's public key, 20-byte payout hex, target roster slot
 * (the NEWSLOT cell of ENDORSE).
 * Output: hex of ENDORSE_DOMAIN + instanceId + cell(tag) + cell(newSlot) +
 * keyHash(newPub) + payout. Binding the slot stops a relayer from writing
 * the endorsed key into a slot the endorser did not choose; binding the
 * instance stops a replay into another machine.
 */
export function endorseMessage(
    instanceIdHex: string,
    tag: bigint,
    newPub: RabinPubKey,
    payoutHex: string,
    newSlot: bigint
): string {
    return (
        ENDORSE_DOMAIN +
        instanceIdHex +
        encodeCell(tag) +
        encodeCell(newSlot) +
        keyHash(newPub) +
        payoutHex
    )
}

/**
 * Sign an endorsement of a new member key into a roster slot.
 * Input: endorser, the machine's instance id hex, tag, new member's public
 * key, payout hex, target slot.
 * Output: Rabin signature over endorseMessage.
 */
export function signEndorsement(
    endorser: Attester,
    instanceIdHex: string,
    tag: bigint,
    newPub: RabinPubKey,
    payoutHex: string,
    newSlot: bigint
): RabinSig {
    return canonicalSig(
        toRabinSig(
            rabin.sign(
                endorseMessage(instanceIdHex, tag, newPub, payoutHex, newSlot),
                endorser.priv
            )
        ),
        endorser.pub
    )
}

/**
 * Payout identity of an address. Input: bsv address. Output: its 20-byte
 * public-key-hash as 40 hex characters.
 */
export function payoutOf(address: bsv.Address): string {
    return address.hashBuffer.toString('hex')
}

/**
 * Domain prefix of a member attestation, ASCII "K17T" (tree roster). Kept
 * apart from the other K17 domains so a signature cannot cross purposes.
 */
export const MEMBER_DOMAIN = '4b313754'

/** Domain prefix of an admission message, ASCII "K17D". */
export const ADMIT_DOMAIN = '4b313744'

/** Domain prefix of a removal message, ASCII "K17X". */
export const REMOVE_DOMAIN = '4b313758'

/**
 * Message a tree-roster member signs for a reading.
 * Input: the machine's 32-byte instance id hex, tag (replay guard), value.
 * Output: hex of MEMBER_DOMAIN + instanceId + cell(tag) + cell(value).
 */
export function memberMessage(
    instanceIdHex: string,
    tag: bigint,
    value: bigint
): string {
    return MEMBER_DOMAIN + instanceIdHex + encodeCell(tag) + encodeCell(value)
}

/**
 * Sign a tree-roster reading.
 * Input: attester, instance id hex, tag, value.
 * Output: Rabin signature over memberMessage.
 */
export function signMemberReading(
    attester: Attester,
    instanceIdHex: string,
    tag: bigint,
    value: bigint
): RabinSig {
    return canonicalSig(
        toRabinSig(
            rabin.sign(memberMessage(instanceIdHex, tag, value), attester.priv)
        ),
        attester.pub
    )
}

/**
 * Message a sponsor signs to admit a new member at a leaf index.
 * Input: instance id hex, tag (replay guard), seq (admission sequence
 * number), leaf index, new member's public key, 20-byte payout hex.
 * Output: hex of ADMIT_DOMAIN + instanceId + cell(tag) + cell(seq) +
 * cell(leafIndex) + keyHash(newPub) + payout.
 */
export function admitMessage(
    instanceIdHex: string,
    tag: bigint,
    seq: bigint,
    leafIndex: bigint,
    newPub: RabinPubKey,
    payoutHex: string
): string {
    return (
        ADMIT_DOMAIN +
        instanceIdHex +
        encodeCell(tag) +
        encodeCell(seq) +
        encodeCell(leafIndex) +
        keyHash(newPub) +
        payoutHex
    )
}

/**
 * Sign an admission.
 * Input: sponsor, instance id hex, tag, seq, leaf index, new member's
 * public key, payout hex.
 * Output: Rabin signature over admitMessage.
 */
export function signAdmission(
    sponsor: Attester,
    instanceIdHex: string,
    tag: bigint,
    seq: bigint,
    leafIndex: bigint,
    newPub: RabinPubKey,
    payoutHex: string
): RabinSig {
    return canonicalSig(
        toRabinSig(
            rabin.sign(
                admitMessage(
                    instanceIdHex,
                    tag,
                    seq,
                    leafIndex,
                    newPub,
                    payoutHex
                ),
                sponsor.priv
            )
        ),
        sponsor.pub
    )
}

/**
 * Message a sponsor signs to remove the member at a leaf index (v3.1).
 * The message binds the member's identity (key hash and payout), not the
 * leaf hash. The leaf also holds lastRound, which every PAYLEAF changes, so
 * a removal signed over the leaf hash stopped verifying after the member
 * was paid. The key hash and payout change only by ADMIT and REMOVE, and
 * those also add one to the roster sequence number in the message.
 * Input: instance id hex, tag, seq (roster sequence number), leaf index,
 * the removed member's 32-byte key hash (64 lowercase hex) and 20-byte
 * payout (40 lowercase hex), that is the first 52 bytes of its leaf
 * preimage.
 * Output: hex of REMOVE_DOMAIN + instanceId + cell(tag) + cell(seq) +
 * cell(leafIndex) + keyHash + payout. Throws when the key hash or the
 * payout is not lowercase hex of the right length.
 */
export function removeMessage(
    instanceIdHex: string,
    tag: bigint,
    seq: bigint,
    leafIndex: bigint,
    keyHashHex: string,
    payoutHex: string
): string {
    if (!/^[0-9a-f]{64}$/.test(keyHashHex)) {
        throw new Error('key hash must be 32 bytes of lowercase hex')
    }
    if (!/^[0-9a-f]{40}$/.test(payoutHex)) {
        throw new Error('payout must be 20 bytes of lowercase hex')
    }
    return (
        REMOVE_DOMAIN +
        instanceIdHex +
        encodeCell(tag) +
        encodeCell(seq) +
        encodeCell(leafIndex) +
        keyHashHex +
        payoutHex
    )
}

/**
 * Sign a removal.
 * Input: sponsor, instance id hex, tag, seq, leaf index, the removed
 * member's key hash hex (64) and payout hex (40).
 * Output: Rabin signature over removeMessage. Throws as removeMessage does.
 */
export function signRemoval(
    sponsor: Attester,
    instanceIdHex: string,
    tag: bigint,
    seq: bigint,
    leafIndex: bigint,
    keyHashHex: string,
    payoutHex: string
): RabinSig {
    return canonicalSig(
        toRabinSig(
            rabin.sign(
                removeMessage(
                    instanceIdHex,
                    tag,
                    seq,
                    leafIndex,
                    keyHashHex,
                    payoutHex
                ),
                sponsor.priv
            )
        ),
        sponsor.pub
    )
}
