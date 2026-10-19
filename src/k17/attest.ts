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
    return toRabinSig(rabin.sign(attestMessage(tag, value), attester.priv))
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
 * Input: tag (replay guard), new member's public key, 20-byte payout hex,
 * target roster slot (the NEWSLOT cell of ENDORSE).
 * Output: hex of ENDORSE_DOMAIN + cell(tag) + cell(newSlot) +
 * keyHash(newPub) + payout. Binding the slot stops a relayer from writing
 * the endorsed key into a slot the endorser did not choose.
 */
export function endorseMessage(
    tag: bigint,
    newPub: RabinPubKey,
    payoutHex: string,
    newSlot: bigint
): string {
    return (
        ENDORSE_DOMAIN +
        encodeCell(tag) +
        encodeCell(newSlot) +
        keyHash(newPub) +
        payoutHex
    )
}

/**
 * Sign an endorsement of a new member key into a roster slot.
 * Input: endorser, tag, new member's public key, payout hex, target slot.
 * Output: Rabin signature over endorseMessage.
 */
export function signEndorsement(
    endorser: Attester,
    tag: bigint,
    newPub: RabinPubKey,
    payoutHex: string,
    newSlot: bigint
): RabinSig {
    return toRabinSig(
        rabin.sign(
            endorseMessage(tag, newPub, payoutHex, newSlot),
            endorser.priv
        )
    )
}

/**
 * Payout identity of an address. Input: bsv address. Output: its 20-byte
 * public-key-hash as 40 hex characters.
 */
export function payoutOf(address: bsv.Address): string {
    return address.hashBuffer.toString('hex')
}
