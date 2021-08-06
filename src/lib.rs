#[macro_use]
extern crate async_trait;

mod async_result;
mod block_in_place_result;
mod map_iterator;
mod merge;
mod tap;

pub use async_result::{AsyncResult, IntoAsync, IntoSync};
pub use block_in_place_result::BlockInPlaceResult;
pub use map_iterator::ResultMapIterator;
pub use merge::Merge;
pub use tap::{Tap, TapErr, TapErrRef, TapRef, ThreadTap, ThreadTapErr};
