// Generated from F* HTMX verification
export const generateSkillLoadAttributes = () => ({
  "hx-get": "/api/skills",
  "hx-target": "#skill-list",
  "hx-swap": "innerHTML"
});

export const generateSkillSearchAttributes = () => ({
  "hx-get": "/api/skills/search",
  "hx-trigger": "keyup changed delay:300ms",
  "hx-target": "#skill-list"
});

export const generateSkillDeleteAttributes = (id) => ({
  "hx-delete": `/api/skills/${id}`,
  "hx-confirm": "Are you sure?",
  "hx-target": "closest .skill-card",
  "hx-swap": "outerHTML"
});
