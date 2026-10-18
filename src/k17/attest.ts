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
import { attestMessage } from './isa'

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
