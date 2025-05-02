use ark_ec::pairing::Pairing;
use ark_std::test_rng;
use std::fmt::{Display, Formatter};
use std::ops::Range;
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use protocol_lib::components::vspark::sqrt_vspark::bench_parts::{build_sqrt_vspark_data, run_sqrt_vspark, VsparkTestcaseData};
use protocol_lib::components::vspark::sqrt_vspark::Vspark;
use ark_bn254::Fq as F;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use protocol_lib::test_utils::data::load_or_generate_data;
fn bench_sqrt_vspark(c: &mut Criterion) {
    let mut group = c.benchmark_group("sqrt_vspark");
    let rng = &mut test_rng();
    let vspark = Vspark::<F>::new(
        20,
        11,
        4,
        20,
        11,
        4,
        3,
        10,
    );

    let test_data = load_or_generate_data("sqrt-vspark", build_sqrt_vspark_data, rng, &vspark);
    
    group.bench_with_input(
        BenchmarkId::new("sqrt_vspark", format!("{:?}", vspark)),
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