use std::{
    fs::OpenOptions,
    io::Write,
    time::{Duration, Instant},
};

use ark_crypto_primitives::{
    crh::{CRHScheme, TwoToOneCRHScheme},
    merkle_tree::Config,
};
use ark_ff::{FftField, Field};
use ark_serialize::CanonicalSerialize;
use clap::Parser;
use serde::Serialize;
use spongefish::{DomainSeparator, ProverState, VerifierState};
use spongefish_pow::blake3::Blake3PoW;
use whir::{
    cmdline_utils::{AvailableFields, AvailableMerkle},
    crypto::{
        fields,
        merkle_tree::{
            blake3::{Blake3Compress, Blake3LeafHash, Blake3MerkleTreeParams},
            keccak::{KeccakCompress, KeccakLeafHash, KeccakMerkleTreeParams},
            parameters::default_config,
            HashCounter,
        },
    },
    parameters::{
        default_max_pow, FoldingFactor, MultivariateParameters, ProtocolParameters, SoundnessType,
    },
    poly_utils::{coeffs::CoefficientList, multilinear::MultilinearPoint},
    whir::{
        committer::CommitmentReader,
        domainsep::DigestDomainSeparator,
        statement::{Statement, Weights},
        utils::{DigestToUnitDeserialize, DigestToUnitSerialize},
    },
};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(short = 'l', long, default_value = "100")]
    security_level: usize,

    #[arg(short = 'p', long)]
    pow_bits: Option<usize>,

    #[arg(short = 'd', long, default_value = "20")]
    num_variables: usize,

    #[arg(short = 'e', long = "evaluations", default_value = "1")]
    num_evaluations: usize,

    #[arg(short = 'r', long, default_value = "1")]
    rate: usize,

    #[arg(long = "reps", default_value = "1000")]
    verifier_repetitions: usize,

    #[arg(short = 'i', long = "initfold", default_value = "4")]
    first_round_folding_factor: usize,

    #[arg(short = 'k', long = "fold", default_value = "4")]
    folding_factor: usize,

    #[arg(long = "sec", default_value = "ConjectureList")]
    soundness_type: SoundnessType,

    #[arg(short = 'f', long = "field", default_value = "Goldilocks2")]
    field: AvailableFields,

    #[arg(long = "hash", default_value = "Blake3")]
    merkle_tree: AvailableMerkle,
}

#[derive(Debug, Serialize)]
struct BenchmarkOutput {
    security_level: usize,
    pow_bits: usize,
    starting_rate: usize,
    num_variables: usize,
    repetitions: usize,
    folding_factor: usize,
    soundness_type: SoundnessType,
    field: AvailableFields,
    merkle_tree: AvailableMerkle,

    // Whir
    whir_evaluations: usize,
    whir_argument_size: usize,
    whir_prover_time: Duration,
    whir_prover_hashes: usize,
    whir_verifier_time: Duration,
    whir_verifier_hashes: usize,

    // Whir LDT
    whir_ldt_argument_size: usize,
    whir_ldt_prover_time: Duration,
    whir_ldt_prover_hashes: usize,
    whir_ldt_verifier_time: Duration,
    whir_ldt_verifier_hashes: usize,
}

type PowStrategy = Blake3PoW;

fn main() {
    let mut args = Args::parse();
    let field = args.field;
    let merkle = args.merkle_tree;

    if args.pow_bits.is_none() {
        args.pow_bits = Some(default_max_pow(args.num_variables, args.rate));
    }

    let mut rng = ark_std::test_rng();

    match (field, merkle) {
        (AvailableFields::Goldilocks1, AvailableMerkle::Blake3) => {
            use fields::Field64 as F;

            let (leaf_hash_params, two_to_one_params) =
                default_config::<F, Blake3LeafHash<F>, Blake3Compress>(&mut rng);
            run_whir::<F, Blake3MerkleTreeParams<F>>(&args, leaf_hash_params, two_to_one_params);
        }

        (AvailableFields::Goldilocks1, AvailableMerkle::Keccak256) => {
            use fields::Field64 as F;

            let (leaf_hash_params, two_to_one_params) =
                default_config::<F, KeccakLeafHash<F>, KeccakCompress>(&mut rng);
            run_whir::<F, KeccakMerkleTreeParams<F>>(&args, leaf_hash_params, two_to_one_params);
        }

        (AvailableFields::Goldilocks2, AvailableMerkle::Blake3) => {
            use fields::Field64_2 as F;

            let (leaf_hash_params, two_to_one_params) =
                default_config::<F, Blake3LeafHash<F>, Blake3Compress>(&mut rng);
            run_whir::<F, Blake3MerkleTreeParams<F>>(&args, leaf_hash_params, two_to_one_params);
        }

        (AvailableFields::Goldilocks2, AvailableMerkle::Keccak256) => {
            use fields::Field64_2 as F;

            let (leaf_hash_params, two_to_one_params) =
                default_config::<F, KeccakLeafHash<F>, KeccakCompress>(&mut rng);
            run_whir::<F, KeccakMerkleTreeParams<F>>(&args, leaf_hash_params, two_to_one_params);
        }

        (AvailableFields::Goldilocks3, AvailableMerkle::Blake3) => {
            use fields::Field64_3 as F;

            let (leaf_hash_params, two_to_one_params) =
                default_config::<F, Blake3LeafHash<F>, Blake3Compress>(&mut rng);
            run_whir::<F, Blake3MerkleTreeParams<F>>(&args, leaf_hash_params, two_to_one_params);
        }

        (AvailableFields::Goldilocks3, AvailableMerkle::Keccak256) => {
            use fields::Field64_3 as F;

            let (leaf_hash_params, two_to_one_params) =
                default_config::<F, KeccakLeafHash<F>, KeccakCompress>(&mut rng);
            run_whir::<F, KeccakMerkleTreeParams<F>>(&args, leaf_hash_params, two_to_one_params);
        }

        (AvailableFields::Field128, AvailableMerkle::Blake3) => {
            use fields::Field128 as F;

            let (leaf_hash_params, two_to_one_params) =
                default_config::<F, Blake3LeafHash<F>, Blake3Compress>(&mut rng);
            run_whir::<F, Blake3MerkleTreeParams<F>>(&args, leaf_hash_params, two_to_one_params);
        }

        (AvailableFields::Field128, AvailableMerkle::Keccak256) => {
            use fields::Field128 as F;

            let (leaf_hash_params, two_to_one_params) =
                default_config::<F, KeccakLeafHash<F>, KeccakCompress>(&mut rng);
            run_whir::<F, KeccakMerkleTreeParams<F>>(&args, leaf_hash_params, two_to_one_params);
        }

        (AvailableFields::Field192, AvailableMerkle::Blake3) => {
            use fields::Field192 as F;

            let (leaf_hash_params, two_to_one_params) =
                default_config::<F, Blake3LeafHash<F>, Blake3Compress>(&mut rng);
            run_whir::<F, Blake3MerkleTreeParams<F>>(&args, leaf_hash_params, two_to_one_params);
        }

        (AvailableFields::Field192, AvailableMerkle::Keccak256) => {
            use fields::Field192 as F;

            let (leaf_hash_params, two_to_one_params) =
                default_config::<F, KeccakLeafHash<F>, KeccakCompress>(&mut rng);
            run_whir::<F, KeccakMerkleTreeParams<F>>(&args, leaf_hash_params, two_to_one_params);
        }

        (AvailableFields::Field256, AvailableMerkle::Blake3) => {
            use fields::Field256 as F;

            let (leaf_hash_params, two_to_one_params) =
                default_config::<F, Blake3LeafHash<F>, Blake3Compress>(&mut rng);

            run_whir::<F, Blake3MerkleTreeParams<F>>(&args, leaf_hash_params, two_to_one_params);
        }

        (AvailableFields::Field256, AvailableMerkle::Keccak256) => {
            use fields::Field256 as F;

            let (leaf_hash_params, two_to_one_params) =
                default_config::<F, KeccakLeafHash<F>, KeccakCompress>(&mut rng);
            run_whir::<F, KeccakMerkleTreeParams<F>>(&args, leaf_hash_params, two_to_one_params);
        }
    }
}

#[allow(clippy::too_many_lines)]
fn run_whir<F, MerkleConfig>(
    args: &Args,
    leaf_hash_params: <<MerkleConfig as Config>::LeafHash as CRHScheme>::Parameters,
    two_to_one_params: <<MerkleConfig as Config>::TwoToOneHash as TwoToOneCRHScheme>::Parameters,
) where
    F: FftField + CanonicalSerialize,
    MerkleConfig: Config<Leaf = [F]> + Clone,
    MerkleConfig::InnerDigest: AsRef<[u8]> + From<[u8; 32]>,
    DomainSeparator: DigestDomainSeparator<MerkleConfig>,
    ProverState: DigestToUnitSerialize<MerkleConfig>,
    for<'a> VerifierState<'a>: DigestToUnitDeserialize<MerkleConfig>,
{
    let security_level = args.security_level;
    let pow_bits = args.pow_bits.unwrap();
    let num_variables = args.num_variables;
    let starting_rate = args.rate;
    let reps = args.verifier_repetitions;
    let folding_factor = args.folding_factor;
    let first_round_folding_factor = args.first_round_folding_factor;
    let soundness_type = args.soundness_type;

    std::fs::create_dir_all("outputs").unwrap();

    let num_coeffs = 1 << num_variables;

    let mv_params = MultivariateParameters::<F>::new(num_variables);

    let whir_params = ProtocolParameters::<MerkleConfig, PowStrategy> {
        initial_statement: true,
        security_level,
        pow_bits,
        folding_factor: FoldingFactor::ConstantFromSecondRound(
            first_round_folding_factor,
            folding_factor,
        ),
        leaf_hash_params,
        two_to_one_params,
        soundness_type,
        _pow_parameters: Default::default(),
        starting_log_inv_rate: starting_rate,
    };

    let polynomial = CoefficientList::new(
        (0..num_coeffs)
            .map(<F as Field>::BasePrimeField::from)
            .collect(),
    );

    let (
        whir_ldt_prover_time,
        whir_ldt_argument_size,
        whir_ldt_prover_hashes,
        whir_ldt_verifier_time,
        whir_ldt_verifier_hashes,
    ) = {
        // Run LDT
        use whir::whir::{
            committer::CommitmentWriter, domainsep::WhirDomainSeparator, parameters::WhirConfig,
            prover::Prover, verifier::Verifier,
        };

        let whir_params = ProtocolParameters::<MerkleConfig, PowStrategy> {
            initial_statement: false,
            ..whir_params.clone()
        };
        let params = WhirConfig::<F, MerkleConfig, PowStrategy>::new(mv_params, whir_params);
        if !params.check_pow_bits() {
            println!("WARN: more PoW bits required than what specified.");
        }

        let domainsep = DomainSeparator::new("🌪️")
            .commit_statement(&params)
            .add_whir_proof(&params);

        let mut prover_state = domainsep.to_prover_state();

        let whir_ldt_prover_time = Instant::now();

        HashCounter::reset();

        let committer = CommitmentWriter::new(params.clone());
        let witness = committer
            .commit(&mut prover_state, polynomial.clone())
            .unwrap();

        let prover = Prover(params.clone());

        let statement_new = Statement::<F>::new(num_variables);

        prover
            .prove(&mut prover_state, statement_new.clone(), witness)
            .unwrap();

        let whir_ldt_prover_time = whir_ldt_prover_time.elapsed();
        let whir_ldt_argument_size = prover_state.narg_string().len();
        let whir_ldt_prover_hashes = HashCounter::get();

        // Just not to count that initial inversion (which could be precomputed)
        let commitment_reader = CommitmentReader::new(&params);
        let verifier = Verifier::new(&params);

        HashCounter::reset();
        let whir_ldt_verifier_time = Instant::now();
        for _ in 0..reps {
            let mut verifier_state = domainsep.to_verifier_state(prover_state.narg_string());
            let parsed_commitment = commitment_reader
                .parse_commitment(&mut verifier_state)
                .unwrap();
            verifier
                .verify(&mut verifier_state, &parsed_commitment, &statement_new)
                .unwrap();
        }

        let whir_ldt_verifier_time = whir_ldt_verifier_time.elapsed();
        let whir_ldt_verifier_hashes = HashCounter::get() / reps;

        (
            whir_ldt_prover_time,
            whir_ldt_argument_size,
            whir_ldt_prover_hashes,
            whir_ldt_verifier_time,
            whir_ldt_verifier_hashes,
        )
    };

    let (
        whir_prover_time,
        whir_argument_size,
        whir_prover_hashes,
        whir_verifier_time,
        whir_verifier_hashes,
    ) = {
        // Run PCS
        use whir::whir::{
            committer::CommitmentWriter, domainsep::WhirDomainSeparator, parameters::WhirConfig,
            prover::Prover, verifier::Verifier,
        };

        let params = WhirConfig::<F, MerkleConfig, PowStrategy>::new(mv_params, whir_params);
        if !params.check_pow_bits() {
            println!("WARN: more PoW bits required than what specified.");
        }

        let domainsep = DomainSeparator::new("🌪️")
            .commit_statement(&params)
            .add_whir_proof(&params);

        let mut prover_state = domainsep.to_prover_state();

        let points: Vec<_> = (0..args.num_evaluations)
            .map(|i| MultilinearPoint(vec![F::from(i as u64); num_variables]))
            .collect();

        let mut statement = Statement::<F>::new(num_variables);

        for point in &points {
            let eval = polynomial.evaluate_at_extension(point);
            let weights = Weights::evaluation(point.clone());
            statement.add_constraint(weights, eval);
        }

        HashCounter::reset();
        let whir_prover_time = Instant::now();

        let committer = CommitmentWriter::new(params.clone());
        let witness = committer.commit(&mut prover_state, polynomial).unwrap();

        let prover = Prover(params.clone());

        prover
            .prove(&mut prover_state, statement.clone(), witness)
            .unwrap();

        let whir_prover_time = whir_prover_time.elapsed();
        let whir_argument_size = prover_state.narg_string().len();
        let whir_prover_hashes = HashCounter::get();

        // Just not to count that initial inversion (which could be precomputed)
        let commitment_reader = CommitmentReader::new(&params);
        let verifier = Verifier::new(&params);

        HashCounter::reset();
        let whir_verifier_time = Instant::now();
        for _ in 0..reps {
            let mut verifier_state = domainsep.to_verifier_state(prover_state.narg_string());
            let parsed_commitment = commitment_reader
                .parse_commitment(&mut verifier_state)
                .unwrap();
            verifier
                .verify(&mut verifier_state, &parsed_commitment, &statement)
                .unwrap();
        }

        let whir_verifier_time = whir_verifier_time.elapsed();
        let whir_verifier_hashes = HashCounter::get() / reps;

        (
            whir_prover_time,
            whir_argument_size,
            whir_prover_hashes,
            whir_verifier_time,
            whir_verifier_hashes,
        )
    };

    let output = BenchmarkOutput {
        security_level,
        pow_bits,
        starting_rate,
        num_variables,
        repetitions: reps,
        folding_factor,
        soundness_type,
        field: args.field,
        merkle_tree: args.merkle_tree,

        // Whir
        whir_evaluations: args.num_evaluations,
        whir_prover_time,
        whir_argument_size,
        whir_prover_hashes,
        whir_verifier_time,
        whir_verifier_hashes,

        // Whir LDT
        whir_ldt_prover_time,
        whir_ldt_argument_size,
        whir_ldt_prover_hashes,
        whir_ldt_verifier_time,
        whir_ldt_verifier_hashes,
    };

    let mut out_file = OpenOptions::new()
        .append(true)
        .create(true)
        .open("outputs/bench_output.json")
        .unwrap();
    writeln!(out_file, "{}", serde_json::to_string(&output).unwrap()).unwrap();
}
