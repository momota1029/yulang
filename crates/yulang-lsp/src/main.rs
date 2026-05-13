fn main() {
    eprintln!(
        "warning: the `yulang-ls` binary is deprecated and will be removed in a future release; use `yulang server` from the `yulang` crate instead."
    );
    yulang::server::run_blocking();
}
