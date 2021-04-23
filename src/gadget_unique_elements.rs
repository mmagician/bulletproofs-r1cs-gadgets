extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;

use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof, Variable, Prover, Verifier};
use curve25519_dalek::scalar::Scalar;
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use bulletproofs::r1cs::LinearCombination;
use crate::r1cs_utils::{AllocatedScalar, constrain_lc_with_scalar};
use crate::gadget_zero_nonzero::is_nonzero_gadget;

#[cfg(test)]
mod tests {
    extern crate rand;
    use std::vec;

    use rand::{RngCore, CryptoRng};
    use super::*;
    use curve25519_dalek::ristretto::CompressedRistretto;

    /// Recall formula for partial sum: n*(n+1)/2
    fn get_partial_sum(n: usize) -> usize {
        n * (n + 1) / 2
    }
    
    fn gen_proof_of_uniqueness<R: RngCore + CryptoRng>(set: &[u64], mut rng: &mut R, pc_gens: &PedersenGens, bp_gens: &BulletproofGens, transcript_label: &'static[u8]) -> Result<(R1CSProof, Vec<CompressedRistretto>), R1CSError> {
            let mut prover_transcript = Transcript::new(transcript_label);
            let mut prover = Prover::new(&pc_gens, &mut prover_transcript);
        
            let mut set_commitments = vec![];
            let mut set_variables: Vec<Variable> = vec![];
            
            // First, create the commitments to the set elements
        
            for i in 0..set.len() {
                let element: Scalar = Scalar::from(set[i]);
                let (com_elem, var_elem) = prover.commit(element, Scalar::random(&mut rng));
                set_commitments.push(com_elem);
                set_variables.push(var_elem);
            }

            /// The following vectors will contain the following elements:
            /// [1st-2nd, 1st-3rd, ..., 2nd-3rd, ..., (n-1)th-nth]
            /// there are total of 
            /// n-1 differences for the 1st element
            /// n-2 differences for the 2nd element
            /// ...
            /// 1 difference for the (n-1)th element
            /// nothing left for the nth element, since it was already accounted for in all previous steps
            let mut diff_commitments = vec![];
            let mut diff_variables: Vec<Variable> = vec![];
            let mut diff_inv_commitments = vec![];
            let mut diff_inv_variables: Vec<Variable> = vec![];
        
            for i in 0..set.len() {
                for j in i+1..set.len() {
                    // We should take the difference of each element with every other element, excluding itself (hence start the inner loop at i+1)
                    let diff = Scalar::from(set[i]) - Scalar::from(set[j]);
                    let (comm_diff, var_diff) = prover.commit(diff.clone(), Scalar::random(&mut rng));
                    diff_commitments.push(comm_diff);
                    diff_variables.push(var_diff);
                    
                    // Get the inverse of each element, and commit to it too
                    let diff_inv = diff.invert();
                    let (comm_diff_inv, var_diff_inv) = prover.commit(diff_inv.clone(), Scalar::random(&mut rng));
                    diff_inv_commitments.push(comm_diff_inv);
                    diff_inv_variables.push(var_diff_inv);
                    
                    // Constrain diff == current - next, i.e. diff + next - current == 0
                    let set_lc: LinearCombination = vec![(var_diff, Scalar::one()), (set_variables[j], Scalar::one()), (set_variables[i], -Scalar::one())].iter().collect();
                    prover.constrain(set_lc);
                }
            }
            
            for i in 0..diff_variables.len() {
                let alloc_scal_diff = AllocatedScalar {
                    variable: diff_variables[i],
                    assignment: None,
                };
                
                let alloc_scal_diff_inv = AllocatedScalar {
                    variable: diff_inv_variables[i],
                    assignment: None,
                };
                
                assert!(is_nonzero_gadget(&mut prover, alloc_scal_diff, alloc_scal_diff_inv).is_ok());
            }
        
            let proof = prover.prove(&bp_gens).unwrap();
            // Let's put all committments in one vector
            let mut commitments = vec![];
            commitments.append(&mut set_commitments);
            commitments.append(&mut diff_commitments);
            commitments.append(&mut diff_inv_commitments);
        
            Ok((proof, commitments))
    }

    fn verify_proof_of_uniqueness(set_length: usize, proof: R1CSProof, commitments: Vec<CompressedRistretto>, transcript_label: &'static[u8], pc_gens: &PedersenGens, bp_gens: &BulletproofGens) -> Result<(), R1CSError> {

        let mut verifier_transcript = Transcript::new(transcript_label);
        let mut verifier = Verifier::new(&mut verifier_transcript);

        // set element commitments, as many as the set itself
        let set_commitments = &commitments[0..set_length];

        /// how many differences do we have? 
        /// For 1st element: n-1 differences
        /// All the way down to (n-1)th element with 1 difference (see explanation in generation step)
        /// That's a partial sum from 1 to n-1, in reverse order
        let num_of_diff_commitments: usize = get_partial_sum(set_length - 1);

        // diff commitments
        let diff_commitments = &commitments[set_length..set_length+num_of_diff_commitments];
        
        // diff inv commitments
        let diff_inv_commitments = &commitments[set_length+num_of_diff_commitments..];

        assert!(diff_commitments.len() == diff_inv_commitments.len());

        let mut var_elements = vec![];
        for i in 0..set_length {
            let var_elem = verifier.commit(set_commitments[i]);
            var_elements.push(var_elem);
        }

        let mut var_diffs = vec![];
        let mut var_diffs_inv = vec![];

        // But we also need to verify that the differences actually come from the set itself!
        for i in 0..set_length {
            let allocated_current = AllocatedScalar {
                variable: var_elements[i],
                assignment: None
            };
            for j in i+1..set_length {
                let allocated_next = AllocatedScalar {
                    variable: var_elements[j],
                    assignment: None
                };
                
                /// Some magic below
                /// For each i, j elements, how to find the index in `var_diffs`?
                /// Full formula, disregarding jth position for now & assume `i` starts at 0
                /// is basically a difference of two partial sums
                /// This is needed, since the arithmetic progression is in reverse (n-1, n-2, ..., 1)
                /// [ n*(n-1) - (n-i)*(n-i-1) ] / 2
                /// This gives the position where differences for i'th element start
                let i_pos = ((2*set_length - i - 1) * i) / 2;
                /// now we add the offset for j:
                let offset = j - i - 1;
                /// and combine
                let index = i_pos + offset;
                println!("i: {}, j: {}, index: {}", i, j, index);

                let var_diff = verifier.commit(diff_commitments[index]);
                var_diffs.push(var_diff);
    
                let var_diff_inv = verifier.commit(diff_inv_commitments[index]);
                var_diffs_inv.push(var_diff_inv);
                
                
                // TODO we've already defined these in the above loop, could be re-used
                let allocated_diff = AllocatedScalar {
                    variable: var_diffs[index],
                    assignment: None
                };
                // Diffs are supposed to be: `diff` = `current_set_element` - `next_set_element`
                // So we require `diff` + `next_set_element` == `current_set_element`
                // (and check it for all elements of the set with every other element, hence the double loop)
                let set_lc: LinearCombination = vec![(allocated_diff.variable, Scalar::one()), (allocated_next.variable, Scalar::one()), (allocated_current.variable, -Scalar::one())].iter().collect();
                verifier.constrain(set_lc);
            }
        }
        // Constrain the differences to be non-zero
        for i in 0..num_of_diff_commitments {

            let allocated_diff = AllocatedScalar {
                variable: var_diffs[i],
                assignment: None
            };

            let allocated_diff_inv = AllocatedScalar { 
                variable: var_diffs_inv[i],
                assignment: None
            };

            assert!(is_nonzero_gadget(&mut verifier, allocated_diff, allocated_diff_inv).is_ok());
        };
        verifier.verify(&proof, &pc_gens, &bp_gens)
    }


    #[test]
    fn test_unique_elements() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);
        // Prove knowledge that all elements of the vector are unique, i.e. that we have a set
        
        let mut rng = rand::thread_rng();
        let transcript_label = b"FactorsUnique";

        let set: Vec<u64> = vec![2, 3, 5, 6, 10];

        let (proof, commitments) = gen_proof_of_uniqueness(&set, &mut rng, &pc_gens, &bp_gens, transcript_label).unwrap();
        // assert!(verify_proof_of_uniqueness(&set, proof, commitments, transcript_label, &pc_gens, &bp_gens).is_ok());
        verify_proof_of_uniqueness(set.len(), proof, commitments, transcript_label, &pc_gens, &bp_gens).unwrap();
    }

    #[test]
    fn test_repeated_elements() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);
        // Prove knowledge that all elements of the vector are unique, i.e. that we have a set
        
        let mut rng = rand::thread_rng();
        let transcript_label = b"FactorsRepeated";

        let set: Vec<u64> = vec![2, 3, 3];

        let (proof, commitments) = gen_proof_of_uniqueness(&set, &mut rng, &pc_gens, &bp_gens, transcript_label).unwrap();
        // Verification should fail, as now the set elements aren't unique
        assert!(verify_proof_of_uniqueness(set.len(), proof, commitments, transcript_label, &pc_gens, &bp_gens).is_err());
    }
}
