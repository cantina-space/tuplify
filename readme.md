# Tuplify

[![Crate link]][crates.io] [![Documentation]][docs.rs] ![License]

Utility library that facilitates the use of tuples as generic arguments.

See individual [Traits][trait_doc] for features implementation and detailled examples.

# Examples

## Tuples

```rust
use tuplify::*;

assert_eq!((1, 2).push_back(3), (1, 2, 3));

assert_eq!((Some(1), Some(2), Some(3)).validate(), Some((1, 2, 3)));

assert_eq!((Some(1), Some(2), None::<i32>).validate(), None);

assert_eq!((1, 2).extend((3, 4)), (1, 2, 3, 4));

assert_eq!((1, 2, 3, 4).pop_back(), (4, (1, 2, 3)));

assert_eq!((1, 2, 3, 4).uncons(), (1, (2, 3, 4)));
```

## Heterogenous list

```rust
use tuplify::*;

assert_eq!(hcons![1, 2].push_back(3), hcons![1, 2, 3]);

assert_eq!(hcons![Some(1), Some(2), Some(3)].validate(), Some(hcons![1, 2, 3]));

assert_eq!(hcons![Ok(1), Ok(2), Err::<u32, _>("oh no")].validate(), Err("oh no"));

assert_eq!(hcons![1, 2].extend(hcons![3, 4]), hcons![1, 2, 3, 4]);

assert_eq!(hcons![1, 2, 3, 4].pop_back(), (4, hcons![1, 2, 3]));

assert_eq!(hcons![1, 2, 3, 4].uncons(), (1, hcons![2, 3, 4]));
```


## Contribution

Found a problem or have a suggestion? Feel free to open an issue.

[Crate link]: https://img.shields.io/crates/v/tuplify.svg
[crates.io]: https://crates.io/crates/tuplify/
[Documentation]: https://docs.rs/tuplify/badge.svg
[docs.rs]: https://docs.rs/tuplify
[trait_doc]: https://docs.rs/tuplify/latest/tuplify/index.html#traits
[License]: https://img.shields.io/crates/l/tuplify.svg