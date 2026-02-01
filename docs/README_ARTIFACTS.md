# Verification Artifacts Documentation

This document explains the F* and Dafny verification artifacts generated during compilation.

## Artifact Structure

### F* Artifacts

F* sources are located in `verification/fstar/` and compile to:

**Frontend:**
- `frontend/FStarLang/JS/` - JavaScript modules
- `frontend/FStarLang/CSS/` - Style definitions
- `frontend/FStarLang/Svelte/` - Svelte components
- `frontend/FStarLang/TailWind/` - Tailwind utilities
- `frontend/FStarLang/HTMX/` - HTMX attributes

**Backend:**
- `backend/process/FStarLang/Rust/` - Process management
- `backend/network/FStarLang/Rust/` - Network handling
- `backend/analysis/FStarLang/Python3/` - Data analysis

### Dafny Artifacts

Dafny sources are in `verification/dafny/` and compile to:

**Frontend:**
- `frontend/Dafny/JS/` - JavaScript modules
- `frontend/Dafny/CSS/` - Style definitions
- `frontend/Dafny/Svelte/` - Svelte components
- `frontend/Dafny/TailWind/` - Tailwind utilities
- `frontend/Dafny/AlpineJS/` - Alpine.js components
- `frontend/Dafny/HTMX/` - HTMX templates

**Backend:**
- `backend/process/Dafny/Rust/` - Rust process modules
- `backend/process/Dafny/CSharp/` - C# process classes
- `backend/process/Dafny/Mermaid/` - Process flow diagrams
- `backend/analysis/Dafny/Python3/` - Python analysis
- `backend/network/Dafny/Rust/` - Network modules
- `backend/database/Dafny/[Type]/` - Database interfaces

## Verification Properties

### Correctness Guarantees

All verified modules provide formal guarantees:

1. **Type Safety**: No type errors at runtime
2. **Memory Safety**: No buffer overflows or null pointer errors
3. **Functional Correctness**: Implementations match specifications
4. **Termination**: All functions terminate (no infinite loops)

### Example: Skill Filtering

The `filterByCategory` function is verified to:
- Return only skills matching the specified category
- Preserve all matching skills (no data loss)
- Maintain skill ordering
- Never crash or throw exceptions

### Example: Process Management

Process management is verified to:
- Assign unique process IDs
- Maintain valid process states
- Handle state transitions correctly
- Prevent invalid status updates

## Using Verified Artifacts

### In Frontend Code

```typescript
import { SkillListDafny } from '../frontend/Dafny/JS/SkillListDafny.js';

// Use verified filtering
const filtered = SkillListDafny.filterByCategory(skills, 'Frontend');
```

### In Backend Code

```rust
use crate::backend::process::FStarLang::Rust::*;

// Use verified process creation
let process = ProcessInfo::new(1, "task".to_string(), timestamp);
```

## Recompilation

To recompile after modifying sources:

```bash
./scripts/compile_all.sh
```

This ensures all artifacts stay synchronized with verification sources.
