# Formatting

This file defines the rules of Rust code formatting to follow in this repository.

To format your code, use `cargo fmt`. This command uses the rules set by the `rustfmt.toml` file. If you are unsure
of how one rule works or what it defines, check out [configurations for rustfmt](https://github.com/rust-lang/rustfmt/blob/master/Configurations.md).

More specific rules about how to write the code itself are defined by [Clippy](https://doc.rust-lang.org/stable/clippy/index.html), which you can run by using `cargo clippy`. Its configuration is located in the `Cargo.toml` file. If you
are unsure of how one rule works or what it defines, check out [the interactive list of clippy lints](https://rust-lang.github.io/rust-clippy/master/index.html).

Other rules defined here are not (yet) enforced by `rustfmt`.

## IDE settings

### Setting Clippy as your linter

For [VSCode](https://code.visualstudio.com/) and its derivatives, such as [VSCodium](https://vscodium.com/), if you have
[the `rust-analyzer` extension](https://marketplace.visualstudio.com/items?itemName=rust-lang.rust-analyzer) go to
`Settings` (`Ctrl+,` / gear in the bottom left), and in the `Extensions` section, find `rust-analyzer`.

Under `check`, change `Rust-analyzer > Check: Command` to `clippy`.

### Imports granularity & grouping

The "Quick fix" option is a popular option in many IDEs, but when it implies importing a new thing, it usually follows
an import granularity that is different from the formatting rules. However, in some IDEs you can change that.

For [VSCode](https://code.visualstudio.com/) and its derivatives, such as [VSCodium](https://vscodium.com/), if you have
[the `rust-analyzer` extension](https://marketplace.visualstudio.com/items?itemName=rust-lang.rust-analyzer) go to
`Settings` (`Ctrl+,` / gear in the bottom left), and in the `Extensions` section, find `rust-analyzer`.

Under `imports`, check `Rust-analyzer > Imports > Granularity: Enforce` and set
`Rust-analyzer > Imports > Granularity: Group` to `module`.

### 120-characters line/ruler

For [VSCode](https://code.visualstudio.com/) and its derivatives, such as [VSCodium](https://vscodium.com/), go to
`Settings` (`Ctrl+,` / gear in the bottom left), and in the `Text Editor` section, no subsection, find `Rulers`, then
click on the `Edit in settings.json` link.

In this file, change the `editor.rulers` property to the following:

```json
    "editor.rulers": [
        120
    ],
```

### Newline

For [VSCode](https://code.visualstudio.com/) and its derivatives, such as [VSCodium](https://vscodium.com/), go to
`Settings` (`Ctrl+,` / gear in the bottom left), and in the `Text Editor` section, `Files` subsection,
find `Eol`, and set it to `\n`, then find `Insert Final Newline` and check it.


## Additional rules

### Comprehensible type/variable names

Prefer long but explicit variable names rather than abbreviations, except if those abbreviations are commonly known,
such as `rhs` (Right-Hand Side), `og` (Original), `arr` (Array), `smth` (Something), `tz` (Timezone). The other exception is if the abbreviation relates to
something very close from where it's written.

If you have trouble with space due to long type names, use this second exception to your advantage! For example:

```rs
match something {
    SomeVeryLongTypeNameThatTakesSpace::A => {},
    SomeVeryLongTypeNameThatTakesSpace::B => {},
    SomeVeryLongTypeNameThatTakesSpace::C => {},
    SomeVeryLongTypeNameThatTakesSpace::D => {},
}
```

can be transformed simply by adding type aliases:

```rs
// Acronym
type SVLTNTTS = SomeVeryLongTypeNameThatTakesSpace;
// Or abbreviation
type LongType = SomeVeryLongTypeNameThatTakesSpace;

match something {
    SVLTNTTS::A => {},
    SVLTNTTS::B => {},
    LongType::C => {},
    LongType::D => {},
}
```

Regarding long variable names, in order to use abbreviations that are not commonly known, you must add a comment
explaining the abbreviation. Example:

```rs
// Timepunches
let tps = ...;
// Manager
let mng = ...;
```

(those are abbreviations I've seen without comments in an actual codebase)

### Follow Rust API Guidelines

See [the Rust API Guidelines Checklist](https://rust-lang.github.io/api-guidelines/checklist.html)

### File structure

```rs
// All imports at the top

// File-global constants under imports
const SOME_CONST: u32 = 42;

// A type without other implementations than derived traits can be followed by another type
#[derive(Clone)]
struct SomeStruct;

// All doc comments should be above type attributes
// then followed by code comments
#[derive(Clone)]
struct SomeOtherStruct;

// All implementations (in the file) for a given struct should be right after the declaration of the typ
impl SomeOtherStruct {
    // ...
}

struct SomeGenericStruct<T>(T);

// Implementations should be ordered like this
// Generic implementation (no trait bounds)...
impl<T> SomeGenericStruct<T> {
    // ...
}

// ...then from less trait bound-restricted implementations... 
impl<T: Clone> SomeGenericStruct<T> {
    // ...
}

// ...to more trait bound-restricted implementations...
impl<T: Clone + Debug + Display> SomeGenericStruct<T> {
    // ...
}

// ...then from less trait bound-restricted implementations of other traits...
impl<T> SomeTrait for SomeGenericStruct<T> {
    // ...
}

// ...to more trait-bound restricted implementations of other traits.
impl<T: Clone> From<SomeOtherStruct> for SomeGenericStruct<T> {
    // ...
}

// Implementations of a trait should generally not be present under the trait itself,
// but in the list of implementations of the implementor.
// Unless the trait is implemented in a generic way
trait SomeTrait {}

impl<T: Display> SomeTrait for T {}

// Constants that are related to a type should be declared above the type itself
const MAX_LIFE: u32 = 100;

struct Life {
    amount: u32;
}

impl Life {
    // ...
}

// Abstraction functions should generally be located under the implementation that uses them
// If they are used by multiple implementations, they should be located under the last one that uses them
// (if the abstraction functions are closely related but not all of them are used under the last impl, they should
// stay together)
// If they are pretty generic, use your best judgment or put them under the last implementation that uses them.
fn complex_computing_of_life_amount(a: u32, x: f64, y: f64, z: f64) -> u32 {
    // ...
}
```

Regarding `impl` order, it is not strictly enforced. That is to say that sometimes, it is better to put more detailed
implementations above certain less detailed ones. Moreover, when a trait is defined in a module, implementations of
such traits can also be present under the trait itself instead of under the definition of the implementor.

This is more a matter of best judgment.

### If you have ideas, suggestions, or ideas for improvement, leave a comment

Use a code comment and prefix it with the prefix that fits most: `// TODO:`, `// NOTE:`, `// IDEA:`. Please restrict yourself to those prefixes in order to simplify search for those comments in the future.

If it's a "To Do" thing present in the code, for example when you write a placeholder, use the [`todo!`](https://doc.rust-lang.org/std/macro.todo.html)
macro:

```rs
impl Idk {
    pub fn shiny_thing() {
        todo!("Shiny thing should be very shiny")
    }
}
```

Only use the [`unimplemented!`](https://doc.rust-lang.org/std/macro.unimplemented.html) macro when it's something
**where the omission of implementation for a case is intentional**, as the Rust documentation says:

> The difference between `unimplemented!` and `todo!` is that while `todo!` conveys an intent of implementing
> the functionality later and the message is “not yet implemented”, `unimplemented!` makes no such claims.
> Its message is “not implemented”.

### Explicitness is your friend

Prefer explicit syntax over implicit syntax, unless it is obvious.

```rs
// OK!
let my_number = 10;
let obscure_type: _ = data.get_obscure_thing();

// NOT OK!
fn smth() -> SomeType {
    // ...
    my_data.into()
    // Use SomeType::from(my_data) instead
}
```

### More comments is better than not enough comments

If you want to walk others through your train of thought or through the process, do it.

Of course, it's good to have self-explanatory code, but sometimes comments can add to how understandable
it is to others.

### Funny comments

Funny comments are allowed. Of course, don't abuse it, but a comment about how convoluted something is or a comment
about how the acronym of a type is funny because is spells another thing is totally ok!

"Frustration comments" can also help point to places where the code needs to be improved.

### A subtrait should be implemented after its suptrait

`Clone` before `Copy`, `PartialEq` before `Eq`, `Debug` before `Display`, etc.

Follow this rule both in explicit implementations and when deriving the traits.

### Unit tests should be separated from the code

Normally you would put the `tests` module in the file that it is testing, however, those tests can take a lot of space.

You should prefer creating an adjacent file named the same as the file it is testing, but suffixed with `_tests`.
Example: `shiny.rs`, `shiny_tests.rs`.

Don't forget to declare the test file in the parent module:

```rs
/*
src/
  lib.rs
  shiny.rs
  shiny_tests.rs
*/

// lib.rs
mod shiny;

#[cfg(test)]
mod shiny_tests;
```
