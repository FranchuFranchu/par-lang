pub type ExternalFnRet = std::pin::Pin<Box<dyn Send + std::future::Future<Output = ()>>>;

#[derive(Clone, Copy, Debug, Hash)]
pub struct ExternalFn {
    pub name: &'static str,
    pub function: fn(crate::runtime::Handle) -> ExternalFnRet,
}

impl PartialEq for ExternalFn {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::fn_addr_eq(self.function, other.function)
    }
}

impl Eq for ExternalFn {}
