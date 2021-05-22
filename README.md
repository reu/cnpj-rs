# cnpj-rs

Brazilian CNPJ parsing, validating and formatting library.

```rust
use cnpj::Cnpj;

// Use the `valid` function if all you need is validating a CNPJ number
assert!(cnpj::valid("38521139039"));
assert!(!cnpj::valid("38521139030"));

// Parse into a Cnpj struct if you need formatting and other metadata
let cnpj: Cnpj = "38521139039".parse()?;

assert_eq!(cnpj.formatted().as_str(), "385.211.390-39");
assert_eq!(cnpj.digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);

// Note that the Cnpj struct is guaranteed to always be valid
assert!("38521139030".parse::<Cnpj>().is_err());
```

## no_std support

The library can be used on no_std environments by disabling the `std` flag:

```toml
[dependencies]
cnpj = { version = "0.1", default-features = false }
```

## Random CNPJ generation support

The `rand` feature flag enables random CNPJ generation:

```toml
[dependencies]
cnpj = { version = "0.1", features = ["rand"] }
rand = "0.8"
```

```rust
use cnpj::Cnpj;
use rand;
use rand::Rng;

let cnpj: Cnpj = rand::thread_rng().gen();
```
