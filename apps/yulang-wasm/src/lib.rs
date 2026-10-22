use wasm_bindgen::prelude::*;

/// Run the experimental candidate inference view for one in-memory source file.
#[wasm_bindgen]
pub fn infer(source: &str) -> Result<String, JsError> {
    yu_playground::infer(source, "browser.yu").map_err(|error| JsError::new(&error))
}

/// Render effect-preserving candidate public types from the module's accepted
/// inference result.
#[wasm_bindgen]
pub fn infer_types(source: &str) -> Result<String, JsError> {
    yu_playground::infer_types(source, "browser.yu").map_err(|error| JsError::new(&error))
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

/// Execute all source-scheduled module roots and return ordered captured writes.
#[wasm_bindgen]
pub fn run_module(source: &str, step_budget: u32) -> Result<String, JsError> {
    let events = yu_playground::execute_module_events(
        source,
        "browser.yu",
        step_budget as usize,
        false,
    ).map_err(|error| JsError::new(&error))?;
    let mut json = String::from("[");
    for (index, event) in events.iter().enumerate() {
        if index != 0 { json.push(','); }
        json.push('"');
        for character in event.chars() {
            match character {
                '"' => json.push_str("\\\""),
                '\\' => json.push_str("\\\\"),
                '\n' => json.push_str("\\n"),
                '\r' => json.push_str("\\r"),
                '\t' => json.push_str("\\t"),
                character if character.is_control() => {
                    use std::fmt::Write;
                    write!(json, "\\u{:04x}", character as u32).expect("writing to String");
                }
                character => json.push(character),
            }
        }
        json.push('"');
    }
    json.push(']');
    Ok(json)
}
