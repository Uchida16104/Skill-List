// Generated from F* Process verification
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ProcessStatus {
    Running,
    Completed,
    Failed,
    Pending,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessInfo {
    pub pid: u64,
    pub name: String,
    pub status: ProcessStatus,
    pub created_at: u64,
    pub updated_at: u64,
}

impl ProcessInfo {
    pub fn new(pid: u64, name: String, timestamp: u64) -> Self {
        if Self::is_valid_process_name(&name) {
            ProcessInfo {
                pid,
                name,
                status: ProcessStatus::Pending,
                created_at: timestamp,
                updated_at: timestamp,
            }
        } else {
            ProcessInfo {
                pid: 0,
                name: "invalid".to_string(),
                status: ProcessStatus::Failed,
                created_at: timestamp,
                updated_at: timestamp,
            }
        }
    }
    
    pub fn is_valid_process_name(name: &str) -> bool {
        !name.is_empty() && name.len() <= 255
    }
    
    pub fn update_status(&mut self, new_status: ProcessStatus, timestamp: u64) {
        self.status = new_status;
        self.updated_at = timestamp;
    }
}

pub fn filter_by_status(processes: &[ProcessInfo], target_status: &ProcessStatus) -> Vec<ProcessInfo> {
    processes.iter()
        .filter(|p| &p.status == target_status)
        .cloned()
        .collect()
}

pub fn count_by_status(processes: &[ProcessInfo], target_status: &ProcessStatus) -> usize {
    processes.iter()
        .filter(|p| &p.status == target_status)
        .count()
}
