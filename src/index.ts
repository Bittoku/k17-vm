/**
 * Package entry point. Re-exports the contract, the ISA/assembler and the
 * reference VM so keepers and tests share one import.
 */
export * from './contracts/k17Machine'
export * from './k17/isa'
// The contract still exports its own (v1) ROSTER_SLOTS = 4 key-array size, which collides
// with the ISA's roster-slot count. The ISA is the source of truth for the package surface.
export { ROSTER_SLOTS } from './k17/isa'
export * from './k17/vm'
export * from './k17/programs'
export * from './k17/attest'
export * from './keeper'
