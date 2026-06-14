use std::fmt;

const CONTROL_VM_MAGIC: &str = "YULANG2-CONTROL-VM 1\n";

pub fn encode_control_program(program: &control_vm::Program) -> Result<String, ArtifactError> {
    let mut out = String::from(CONTROL_VM_MAGIC);
    let json = serde_json::to_string(program).map_err(ArtifactError::Encode)?;
    out.push_str(&json);
    out.push('\n');
    Ok(out)
}

pub fn decode_control_program(source: &str) -> Result<Option<control_vm::Program>, ArtifactError> {
    let Some(json) = source.strip_prefix(CONTROL_VM_MAGIC) else {
        return Ok(None);
    };
    let program = serde_json::from_str(json).map_err(ArtifactError::Decode)?;
    Ok(Some(program))
}

#[derive(Debug)]
pub enum ArtifactError {
    Encode(serde_json::Error),
    Decode(serde_json::Error),
}

impl fmt::Display for ArtifactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Encode(error) => write!(f, "failed to encode control-vm artifact: {error}"),
            Self::Decode(error) => write!(f, "failed to decode control-vm artifact: {error}"),
        }
    }
}

impl std::error::Error for ArtifactError {}
