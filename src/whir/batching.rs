#![cfg(feature = "batching")]

use crate::whir::committer::{Committer, Witness};
use crate::whir::parameters::WhirConfig;
use crate::whir::fs_utils::DigestWriter;
use crate::whir::domainsep::{WhirDomainSeparator, DigestDomainSeparator};
use crate::fs_utils::{WhirPoWDomainSeparator, OODDomainSeparator};
use crate::poly_utils::coeffs::CoefficientList;

use crate::sumcheck::SumcheckSingleDomainSeparator;
use spongefish::codecs::arkworks_algebra::{ByteDomainSeparator, FieldDomainSeparator};
use ark_ff::FftField;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use spongefish::codecs::arkworks_algebra::{FieldToUnit, UnitToField, ByteWriter};
use spongefish::{ProofResult, ProofError};

///
/// This is the list of [Witness] structs as if each polynomial will be
/// folded independently. The witnesses are combined after the commitment
/// since the verifier needs to sample its randomness _after_ the merkle
/// root of each polynomial has been added to the FS transcript.
///
pub struct BatchedWitness<F, MerkleConfig:MTConfig>{
    pub(crate) witness_list : Vec<Witness<F, MerkleConfig>>,
    pub(crate) batching_randomness : F
}


pub trait BatchedDomainSeparator<F, MerkleConfig> : WhirDomainSeparator<F, MerkleConfig>
where
    F : FftField,
    MerkleConfig: MTConfig
{
    ///
    ///  FS Batch Commitment state machine:
    ///  P -> V Transcript
    ///     32-bit (4-bytes): Number of entries in the batch
    ///     For each batch entry:
    ///         Prover-<id> : Merkle Root of prover-id
    ///         arity-number of OOD Query field element
    ///         OOD Response for that prover
    ///
    /// Verifier should sample its batching randomness after adding
    /// the above transcript:
    ///   V -> P
    ///         Sample single scalar element
    ///
    #[must_use]
    fn batch_commit_statement<PowStrategy>(
        self,
        batch_size : u32,
        params: &WhirConfig<F, MerkleConfig, PowStrategy>,
    ) -> Self;
}

impl<F, MerkleConfig, DomainSeparator> BatchedDomainSeparator<F, MerkleConfig> for DomainSeparator
where
    F: FftField,
    MerkleConfig: MTConfig,
    DomainSeparator: ByteDomainSeparator
        + FieldDomainSeparator<F>
        + SumcheckSingleDomainSeparator<F>
        + WhirPoWDomainSeparator
        + OODDomainSeparator<F>
        + DigestDomainSeparator<MerkleConfig>,
{
    fn batch_commit_statement<PowStrategy>(
        self,
        batch_size : u32,
        params: &WhirConfig<F, MerkleConfig, PowStrategy>,
    ) -> Self {

        // Add the number of elements that have been batched
        let mut this = self.add_scalars(1, "batch_size");

        for i in 0..batch_size {
            let label = format!("commitment-root-{}", &i);

            // Add the root of each Merkle tree
            this = this.add_digest(&label);

            // Add the OOD samples if present
            if params.committment_ood_samples > 0 {
                assert!(params.initial_statement);
                this = this.add_ood(params.committment_ood_samples);
            }
        }

        // Sample the batching combination randomness
        this.challenge_scalars(1, "batching_randomness")
    }

}


impl <F, MerkleConfig, PowStrategy>  Committer<F, MerkleConfig, PowStrategy>
where
    F : FftField,
    MerkleConfig : MTConfig<Leaf = [F]>
{
    fn add_batchsize_to_transcript<ProverFSState>(
        &self,
        prover_state: &mut ProverFSState,
        batch_size : usize
    ) -> ProofResult<()>
    where
        ProverFSState : FieldToUnit<F>
    {
        let field_element = F::from(batch_size as u32);
        prover_state.add_scalars(&[field_element])
    }

    pub fn batch_commit<ProverFSState>(
        &self,
        prover_state: &mut ProverFSState,
        polynomial_list : &[CoefficientList<F::BasePrimeField>],
    ) -> ProofResult<BatchedWitness<F, MerkleConfig>>
    where
        ProverFSState : FieldToUnit<F> + UnitToField<F> + ByteWriter + DigestWriter<MerkleConfig>,
    {
        assert!(polynomial_list.len() > 1,
            "Batched evaluation requires more than one polynomial"
        );

        assert!(
            polynomial_list.iter().all(
                |poly| {
                    poly.num_variables() == polynomial_list[0].num_variables() &&
                    poly.num_coeffs() == polynomial_list[0].num_coeffs()
                }
            ),
            "Each polynomial must have same number of variables and same number of coefficients"
        );

        self.add_batchsize_to_transcript(prover_state, polynomial_list.len())?;

        let mut witness_list = Vec::new();

        for poly in polynomial_list {
            let virt_commitment = Committer::commit(self, prover_state, poly.clone())?;
            witness_list.push(virt_commitment);
        }

        let [batching_randomness] = prover_state.challenge_scalars()?;

        Ok(BatchedWitness{
            witness_list : witness_list,
            batching_randomness: batching_randomness
        })
    }
}