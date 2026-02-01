// Generated from Dafny Process verification
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DafnyProcess {
    pub id: u64,
    pub name: String,
    pub status: String,
    pub priority: u8,
}

impl DafnyProcess {
    pub fn new(id: u64, name: String, priority: u8) -> Result<Self, String> {
        if Self::validate_priority(priority) {
            Ok(DafnyProcess {
                id,
                name,
                status: "pending".to_string(),
                priority,
            })
        } else {
            Err("Invalid priority: must be between 1 and 10".to_string())
        }
    }
    
    pub fn validate_priority(priority: u8) -> bool {
        priority >= 1 && priority <= 10
    }
}
