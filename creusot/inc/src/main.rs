use creusot_std::prelude::*;

// #[ensures((^x)@ == (x@ + 1))]
// #[requires (x@ < 100)]
// fn increment (x : &mut i32) {
//     *x = *x + 1;
// }

#[ensures ((^src) == dest)]
#[ensures (result == *src)]
fn replace (src : &mut i32, dest : i32) -> i32 {
    let result = *src;
    *src = dest;
    result
}

fn main(){
    let mut x = Box::new(0);
    let y = &mut x;
    replace(y, 1);
    assert!(*x == 1);
}
