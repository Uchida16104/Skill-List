// Main Rust backend server for Skill List application
// Compiled with formally verified F* and Dafny modules

use actix_web::{web, App, HttpResponse, HttpServer, Result, middleware};
use actix_cors::Cors;
use serde::{Deserialize, Serialize};
use std::sync::Mutex;
use std::collections::HashMap;
use log::info;

// Import verified modules
mod handlers;
mod models;

// Include compiled F* and Dafny artifacts
mod process {
    include!("../backend/process/FStarLang/Rust/process.rs");
}

mod network {
    include!("../backend/network/FStarLang/Rust/network.rs");
}

// Shared application state
struct AppState {
    skills: Mutex<HashMap<u64, Skill>>,
    next_id: Mutex<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Skill {
    id: u64,
    name: String,
    category: String,
    level: u8,
    verified: bool,
    created_at: String,
}

impl Skill {
    fn new(id: u64, name: String, category: String, level: u8) -> Self {
        Skill {
            id,
            name,
            category,
            level,
            verified: false,
            created_at: chrono::Utc::now().to_rfc3339(),
        }
    }
}

#[derive(Debug, Deserialize)]
struct CreateSkillRequest {
    name: String,
    category: String,
    level: u8,
}

#[derive(Debug, Deserialize)]
struct UpdateSkillRequest {
    name: Option<String>,
    category: Option<String>,
    level: Option<u8>,
    verified: Option<bool>,
}

// Health check endpoint
async fn health_check() -> HttpResponse {
    HttpResponse::Ok().json(serde_json::json!({
        "status": "healthy",
        "service": "skill-list-backend",
        "version": "0.1.0"
    }))
}

// Get all skills
async fn get_skills(data: web::Data<AppState>) -> Result<HttpResponse> {
    let skills = data.skills.lock().unwrap();
    let skill_list: Vec<&Skill> = skills.values().collect();
    Ok(HttpResponse::Ok().json(skill_list))
}

// Get skill by ID
async fn get_skill(
    data: web::Data<AppState>,
    skill_id: web::Path<u64>,
) -> Result<HttpResponse> {
    let skills = data.skills.lock().unwrap();
    
    match skills.get(&skill_id.into_inner()) {
        Some(skill) => Ok(HttpResponse::Ok().json(skill)),
        None => Ok(HttpResponse::NotFound().json(serde_json::json!({
            "error": "Skill not found"
        }))),
    }
}

// Create new skill
async fn create_skill(
    data: web::Data<AppState>,
    req: web::Json<CreateSkillRequest>,
) -> Result<HttpResponse> {
    // Validate request
    if req.name.is_empty() || req.name.len() > 100 {
        return Ok(HttpResponse::BadRequest().json(serde_json::json!({
            "error": "Skill name must be between 1 and 100 characters"
        })));
    }
    
    if req.level < 1 || req.level > 5 {
        return Ok(HttpResponse::BadRequest().json(serde_json::json!({
            "error": "Skill level must be between 1 and 5"
        })));
    }
    
    let mut skills = data.skills.lock().unwrap();
    let mut next_id = data.next_id.lock().unwrap();
    
    let skill = Skill::new(*next_id, req.name.clone(), req.category.clone(), req.level);
    skills.insert(*next_id, skill.clone());
    *next_id += 1;
    
    Ok(HttpResponse::Created().json(skill))
}

// Update skill
async fn update_skill(
    data: web::Data<AppState>,
    skill_id: web::Path<u64>,
    req: web::Json<UpdateSkillRequest>,
) -> Result<HttpResponse> {
    let mut skills = data.skills.lock().unwrap();
    let id = skill_id.into_inner();
    
    match skills.get_mut(&id) {
        Some(skill) => {
            if let Some(name) = &req.name {
                if !name.is_empty() && name.len() <= 100 {
                    skill.name = name.clone();
                }
            }
            if let Some(category) = &req.category {
                skill.category = category.clone();
            }
            if let Some(level) = req.level {
                if level >= 1 && level <= 5 {
                    skill.level = level;
                }
            }
            if let Some(verified) = req.verified {
                skill.verified = verified;
            }
            
            Ok(HttpResponse::Ok().json(skill.clone()))
        }
        None => Ok(HttpResponse::NotFound().json(serde_json::json!({
            "error": "Skill not found"
        }))),
    }
}

// Delete skill
async fn delete_skill(
    data: web::Data<AppState>,
    skill_id: web::Path<u64>,
) -> Result<HttpResponse> {
    let mut skills = data.skills.lock().unwrap();
    
    match skills.remove(&skill_id.into_inner()) {
        Some(_) => Ok(HttpResponse::Ok().json(serde_json::json!({
            "message": "Skill deleted successfully"
        }))),
        None => Ok(HttpResponse::NotFound().json(serde_json::json!({
            "error": "Skill not found"
        }))),
    }
}

// Search skills
async fn search_skills(
    data: web::Data<AppState>,
    query: web::Query<HashMap<String, String>>,
) -> Result<HttpResponse> {
    let skills = data.skills.lock().unwrap();
    let search_term = query.get("q").map(|s| s.to_lowercase());
    let category_filter = query.get("category");
    
    let mut filtered: Vec<&Skill> = skills.values().collect();
    
    if let Some(term) = search_term {
        filtered.retain(|s| s.name.to_lowercase().contains(&term));
    }
    
    if let Some(cat) = category_filter {
        filtered.retain(|s| &s.category == cat);
    }
    
    Ok(HttpResponse::Ok().json(filtered))
}

// Get unique categories
async fn get_categories(data: web::Data<AppState>) -> Result<HttpResponse> {
    let skills = data.skills.lock().unwrap();
    let mut categories: Vec<String> = skills
        .values()
        .map(|s| s.category.clone())
        .collect();
    categories.sort();
    categories.dedup();
    
    Ok(HttpResponse::Ok().json(categories))
}

// Get statistics
async fn get_statistics(data: web::Data<AppState>) -> Result<HttpResponse> {
    let skills = data.skills.lock().unwrap();
    let total = skills.len();
    let verified = skills.values().filter(|s| s.verified).count();
    
    let mut by_category: HashMap<String, usize> = HashMap::new();
    for skill in skills.values() {
        *by_category.entry(skill.category.clone()).or_insert(0) += 1;
    }
    
    Ok(HttpResponse::Ok().json(serde_json::json!({
        "total_skills": total,
        "verified_skills": verified,
        "by_category": by_category,
    })))
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // Initialize logging
    env_logger::init_from_env(env_logger::Env::default().default_filter_or("info"));
    
    // Load environment variables
    dotenv::dotenv().ok();
    
    let port = std::env::var("PORT")
        .unwrap_or_else(|_| "10000".to_string())
        .parse::<u16>()
        .expect("PORT must be a valid number");
    
    let host = std::env::var("HOST").unwrap_or_else(|_| "0.0.0.0".to_string());
    
    info!("Starting Skill List Backend Server");
    info!("Listening on {}:{}", host, port);
    
    // Initialize application state with sample data
    let app_state = web::Data::new(AppState {
        skills: Mutex::new(HashMap::from([
            (1, Skill::new(1, "Rust Programming".to_string(), "Backend".to_string(), 5)),
            (2, Skill::new(2, "F* Verification".to_string(), "Formal Methods".to_string(), 4)),
            (3, Skill::new(3, "Dafny Proofs".to_string(), "Formal Methods".to_string(), 4)),
            (4, Skill::new(4, "Next.js".to_string(), "Frontend".to_string(), 5)),
        ])),
        next_id: Mutex::new(5),
    });
    
    // Start HTTP server
    HttpServer::new(move || {
        let cors = Cors::permissive();
        
        App::new()
            .app_data(app_state.clone())
            .wrap(cors)
            .wrap(middleware::Logger::default())
            .wrap(middleware::Compress::default())
            .route("/health", web::get().to(health_check))
            .route("/api/skills", web::get().to(get_skills))
            .route("/api/skills", web::post().to(create_skill))
            .route("/api/skills/{id}", web::get().to(get_skill))
            .route("/api/skills/{id}", web::put().to(update_skill))
            .route("/api/skills/{id}", web::delete().to(delete_skill))
            .route("/api/skills/search", web::get().to(search_skills))
            .route("/api/categories", web::get().to(get_categories))
            .route("/api/statistics", web::get().to(get_statistics))
    })
    .bind((host, port))?
    .run()
    .await
}
