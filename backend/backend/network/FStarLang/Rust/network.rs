// Generated from F* Network verification
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RequestMethod {
    GET, POST, PUT, DELETE,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ResponseStatus {
    OK, Created, BadRequest, NotFound, InternalError,
}

impl ResponseStatus {
    pub fn to_code(&self) -> u16 {
        match self {
            ResponseStatus::OK => 200,
            ResponseStatus::Created => 201,
            ResponseStatus::BadRequest => 400,
            ResponseStatus::NotFound => 404,
            ResponseStatus::InternalError => 500,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkResponse {
    pub status: ResponseStatus,
    pub headers: Vec<(String, String)>,
    pub body: String,
}

impl NetworkResponse {
    pub fn new(status: ResponseStatus, body: String) -> Self {
        NetworkResponse {
            status,
            headers: vec![("Content-Type".to_string(), "application/json".to_string())],
            body,
        }
    }
    
    pub fn json(status: ResponseStatus, json_body: String) -> Self {
        NetworkResponse {
            status,
            headers: vec![
                ("Content-Type".to_string(), "application/json".to_string()),
                ("Access-Control-Allow-Origin".to_string(), "*".to_string()),
            ],
            body: json_body,
        }
    }
}

pub fn is_valid_path(path: &str) -> bool {
    !path.is_empty() && path.starts_with('/')
}
