use std::fmt::{Debug, Display};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use crate::components::vspark::sqrt_vspark::bench_parts::{build_sqrt_vspark_data, VsparkTestcaseData};

pub fn load_or_generate_data<Rng, Cfg: Debug, Case: CanonicalSerialize + CanonicalDeserialize, Gen: Fn(&mut Rng, &Cfg) -> Case>(name: impl Display, f: Gen, rng: &mut Rng, cfg: &Cfg) -> Case {
    let bench_path = format!("bench-data/{}: {:?}", name, cfg);
    if !std::fs::exists(bench_path.clone()).unwrap() {
        let test_data = f(rng, &cfg);
        std::fs::create_dir_all(std::path::PathBuf::from(bench_path.clone()).parent().unwrap()).unwrap();
        let file = std::fs::File::create(bench_path.clone()).unwrap();
        test_data.serialize_compressed(file).unwrap();
    }
    let file = std::fs::File::open(bench_path).unwrap();
    Case::deserialize_compressed(file).unwrap()
}