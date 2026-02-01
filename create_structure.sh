#!/bin/bash
set -e

# Root directories
mkdir -p scripts
mkdir -p .github/workflows
mkdir -p docs

# Frontend directories
mkdir -p frontend/app/pages
mkdir -p frontend/app/components
mkdir -p frontend/public
mkdir -p frontend/frontend/Dafny/JS
mkdir -p frontend/frontend/Dafny/CSS
mkdir -p frontend/frontend/Dafny/Svelte
mkdir -p frontend/frontend/Dafny/TailWind
mkdir -p frontend/frontend/Dafny/AlpineJS
mkdir -p frontend/frontend/Dafny/HTMX
mkdir -p frontend/frontend/FStarLang/JS
mkdir -p frontend/frontend/FStarLang/CSS
mkdir -p frontend/frontend/FStarLang/Svelte
mkdir -p frontend/frontend/FStarLang/TailWind
mkdir -p frontend/frontend/FStarLang/HTMX

# Backend directories
mkdir -p backend/src/handlers
mkdir -p backend/src/models
mkdir -p backend/backend/process/Dafny/Mermaid
mkdir -p backend/backend/process/Dafny/CSharp
mkdir -p backend/backend/process/Dafny/Rust
mkdir -p backend/backend/process/FStarLang/CSharp
mkdir -p backend/backend/process/FStarLang/Rust
mkdir -p backend/backend/analysis/Dafny/Mermaid
mkdir -p backend/backend/analysis/Dafny/Python3
mkdir -p backend/backend/analysis/FStarLang/Python3
mkdir -p backend/backend/network/Dafny/Mermaid
mkdir -p backend/backend/network/Dafny/Rust
mkdir -p backend/backend/network/FStarLang/Rust
mkdir -p backend/backend/database/Dafny/Mermaid
mkdir -p backend/backend/database/Dafny/IndexedDB
mkdir -p backend/backend/database/Dafny/PouchDB
mkdir -p backend/backend/database/Dafny/LocalStorage
mkdir -p backend/backend/database/Dafny/SQLJS
mkdir -p backend/backend/database/FStarLang/IndexedDB
mkdir -p backend/backend/database/FStarLang/PouchDB
mkdir -p backend/backend/database/FStarLang/LocalStorage
mkdir -p backend/backend/database/FStarLang/SQLJS

# F* source directories (pre-compilation)
mkdir -p verification/fstar/frontend/js
mkdir -p verification/fstar/frontend/css
mkdir -p verification/fstar/frontend/svelte
mkdir -p verification/fstar/frontend/tailwind
mkdir -p verification/fstar/frontend/htmx
mkdir -p verification/fstar/backend/process
mkdir -p verification/fstar/backend/network
mkdir -p verification/fstar/backend/analysis
mkdir -p verification/fstar/backend/database

# Dafny source directories (pre-compilation)
mkdir -p verification/dafny/frontend/js
mkdir -p verification/dafny/frontend/css
mkdir -p verification/dafny/frontend/svelte
mkdir -p verification/dafny/frontend/tailwind
mkdir -p verification/dafny/frontend/alpinejs
mkdir -p verification/dafny/frontend/htmx
mkdir -p verification/dafny/backend/process
mkdir -p verification/dafny/backend/analysis
mkdir -p verification/dafny/backend/network
mkdir -p verification/dafny/backend/database

echo "Directory structure created successfully"
