# cnpj-rs

Brazilian CNPJ parsing, validating and formatting library.

```rust
use cnpj::Cnpj;

// Use the `valid` function if all you need is validating a CNPJ number
assert!(cnpj::valid("96.769.900/0001-77"));
assert!(cnpj::valid("96769900000177"));
assert!(!cnpj::valid("00.000.000/0000-00"));

// Parse into a Cnpj struct if you need formatting or other metadata
let cnpj: Cnpj = "96769900000177".parse()?;
assert_eq!(format!("{}", cnpj), "96.769.900/0001-77");
assert_eq!(cnpj.digits(), [9, 6, 7, 6, 9, 9, 0, 0, 0, 0, 0, 1, 7, 7]);

// Note that the Cnpj struct is guaranteed to always be valid
assert!("00.000.000/0000-00".parse::<Cnpj>().is_err());
assert!(cnpj::valid("96.769.900/0001-77".parse::<Cnpj>()?));
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
