# Tuplify

[![Crate link]][crates.io] [![Documentation]][docs.rs] ![License]

Utility library that facilitates the use of tuples as generic arguments.

Most of the available features are documented in the [`hlist`](https://docs.rs/tuplify/latest/tuplify/hlist/index.html) module.

# Examples

```rust
use tuplify::*;

assert_eq!((1, 2).push_back(3), (1, 2, 3));

assert_eq!((Some(1), Some(2), Some(3)).validate(), Some((1, 2, 3)));

assert_eq!((Some(1), Some(2), None::<i32>).validate(), None);

assert_eq!((1, 2).extend((3, 4)), (1, 2, 3, 4));

assert_eq!((1, 2, 3, 4).pop_back(), (4, (1, 2, 3)));

assert_eq!((1, 2, 3, 4).uncons(), (1, (2, 3, 4)));
```

## Contribution

Found a problem or have a suggestion? Feel free to open an issue.

[Crate link]: https://img.shields.io/crates/v/tuplify.svg
[crates.io]: https://crates.io/crates/tuplify/
[Documentation]: https://docs.rs/tuplify/badge.svg
[docs.rs]: https://docs.rs/tuplify
[License]: https://img.shields.io/crates/l/tuplify.svg