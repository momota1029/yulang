use wasm_bindgen::prelude::*;

/// Run the experimental candidate inference view for one in-memory source file.
#[wasm_bindgen]
pub fn infer(source: &str) -> Result<String, JsError> {
    yu_playground::infer(source, "browser.yu").map_err(|error| JsError::new(&error))
}

/// Execute one selected definition using the current provisional source evaluator.
#[wasm_bindgen]
pub fn run(source: &str, definition: &str, step_budget: u32) -> Result<String, JsError> {
    yu_playground::execute(
        source,
        "browser.yu",
        definition,
        step_budget as usize,
        false,
    )
    .map_err(|error| JsError::new(&error))
}
