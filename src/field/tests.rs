#[cfg(test)]
mod tests {
    use std::time::Instant;
    use ark_ff::UniformRand;
    use ark_std::test_rng;
    use itertools::Itertools;
    use rayon::prelude::*;
    use crate::field::f128_polyval::field::F128;
    use crate::common::math::eq_poly;
    use ark_bn254::Fq as F254;
 
    #[test]
    fn field_speed_test() {
        let n = 20;
        let rng = &mut test_rng();
        let mut data_1 = (1 .. 1 << n).map(|_| F128::rand(rng)).collect_vec();
        let mul_by_1 = F128::rand(rng);
        let mut data_2 = (1 .. 1 << n).map(|_| F254::rand(rng)).collect_vec();
        let mul_by_2 = F254::rand(rng);

        let start = Instant::now();
        

        data_1.iter_mut().map(|x| *x *= mul_by_1).count();
        let finish = Instant::now();
        println!("Time to do 2^{} mults: {} ms in F128", n, (finish - start).as_millis());

        let start = Instant::now();
        data_1.par_iter_mut().map(|x| *x *= mul_by_1).count();
        let finish = Instant::now();
        println!("Time to do parallel iterator 2^{} mults: {} ms in F128", n, (finish - start).as_millis());

        let start = Instant::now();
        let num_threads = rayon::current_num_threads();
        let len = data_1.len();
        // Compute the chunk size with rounding up so that all elements are covered.
        let chunk_size = (len + num_threads - 1) / num_threads;
        
        rayon::scope(|s| {
            for chunk in data_1.chunks_mut(chunk_size) {
                s.spawn(move |_| {
                    for x in chunk {
                        *x *= mul_by_1;
                    }
                });
            }
        });
        let finish = Instant::now();
        println!("Time to do 2^{} mults using scope / join: {} ms in F128", n, (finish - start).as_millis());

        let start = Instant::now();
        data_2.iter_mut().map(|x| *x *= mul_by_2).count();
        let finish = Instant::now();
        println!("Time to do 2^{} mults: {} ms in F254", n, (finish - start).as_millis());

        let start = Instant::now();
        data_2.par_iter_mut().map(|x| *x *= mul_by_2).count();
        let finish = Instant::now();
        println!("Time to do parallel 2^{} mults: {} ms in F254", n, (finish - start).as_millis());

        let start = Instant::now();
        let num_threads = rayon::current_num_threads();
        let len = data_2.len();
        // Compute the chunk size with rounding up so that all elements are covered.
        let chunk_size = (len + num_threads - 1) / num_threads;
        
        rayon::scope(|s| {
            for chunk in data_2.chunks_mut(chunk_size) {
                s.spawn(move |_| {
                    for x in chunk {
                        *x *= mul_by_2;
                    }
                });
            }
        });
        let finish = Instant::now();
        println!("Time to do 2^{} mults using scope / join: {} ms in F254", n, (finish - start).as_millis());


    }

    #[test]
    fn eq_poly_speed() {
    
        let rng = &mut test_rng();

        for n in 0..26 {    
            let point = (0..n).map(|_| F128::rand(rng)).collect_vec();   
            let start = Instant::now();
            let s = eq_poly(&point);
            let finish = Instant::now();
            println!("F128: n {} | time: {} mcs", n, (finish - start).as_micros());
        }
        for n in 0..26 {    
            let point = (0..n).map(|_| F254::rand(rng)).collect_vec();   
            let start = Instant::now();
            let s = eq_poly(&point);
            let finish = Instant::now();
            println!("F254: n {} | time: {} mcs", n, (finish - start).as_micros());

            if n == 0 {
                println!("{:?}", s);
            }
        }
    }
}