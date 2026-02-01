// Generated from Dafny Network verification
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DafnyRequest {
    pub method: String,
    pub path: String,
    pub body: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DafnyResponse {
    pub status_code: u16,
    pub body: String,
    pub content_type: String,
}

impl DafnyResponse {
    pub fn success(body: String) -> Self {
        DafnyResponse {
            status_code: 200,
            body,
            content_type: "application/json".to_string(),
        }
    }
    
    pub fn error(status_code: u16, message: String) -> Self {
        DafnyResponse {
            status_code,
            body: format!(r#"{{"error":"{}"}}"#, message),
            content_type: "application/json".to_string(),
        }
    }
}

pub fn validate_path(path: &str) -> bool {
    !path.is_empty() && path.starts_with('/') && path.len() < 2000
}
