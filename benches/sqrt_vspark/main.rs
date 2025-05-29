use ark_ec::pairing::Pairing;
use ark_std::test_rng;
use std::fmt::{Display, Formatter};
use std::ops::Range;
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use protocol_lib::components::vspark::sqrt_vspark::bench_parts::{build_sqrt_vspark_data, run_sqrt_vspark, VsparkTestcaseData};
use protocol_lib::components::vspark::sqrt_vspark::{VsparkConfig, VsparkProver};
use ark_bn254::Fr as F;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use protocol_lib::components::commitments::knuckles::KnucklesProvingKey;
use protocol_lib::test_utils::data::load_or_generate_data;
fn bench_sqrt_vspark(c: &mut Criterion) {
    let mut group = c.benchmark_group("sqrt_vspark");
    let rng = &mut test_rng();
    let vspark_config = VsparkConfig::<F>::new(
        20,
        11,
        4,
        20,
        11,
        4,
        3,
        10,
    );

    let test_data = load_or_generate_data("sqrt-vspark", build_sqrt_vspark_data, rng, &vspark_config);
    let knuckles_pk = KnucklesProvingKey::<ark_bn254::Bn254>::build(test_data.knuckles_setup);
    let vspark = VsparkProver {
        config: vspark_config.clone(),
        commitment_scheme: knuckles_pk,
    };
    let test_data = VsparkTestcaseData {
        prover_input: test_data.prover_input,
        eval_claim: test_data.eval_claim,
    };
    group.bench_with_input(
        BenchmarkId::new("sqrt_vspark", format!("{:?}", vspark_config)),
        &test_data,
        |b, i| {
            b.iter_batched(
                || i.clone(),
                |i| run_sqrt_vspark(&vspark, i),
                BatchSize::SmallInput,
            )
        }
    );
    group.finish();
}

criterion_group!(benches, bench_sqrt_vspark);
criterion_main!(benches);