use std::error::Error;

/// Any error
/// 
/// Used to easily allow tests to use `?` on [`Result`]s with different error types
#[derive(Debug)]
pub struct AnyError(pub Box<dyn Error>);

impl<E> From<E> for AnyError
where
    E: Error + 'static,
{
    fn from(value: E) -> Self {
        AnyError(Box::new(value))
    }
}

pub type TestResult = Result<(), AnyError>;
