// Generated from Dafny Alpine.js verification
document.addEventListener('alpine:init', () => {
  Alpine.data('skillList', () => ({
    skills: [],
    searchQuery: '',
    selectedCategory: null,
    
    init() {
      this.loadSkills();
    },
    
    get filteredSkills() {
      let result = this.skills;
      
      if (this.searchQuery) {
        result = result.filter(s => 
          s.name.toLowerCase().includes(this.searchQuery.toLowerCase())
        );
      }
      
      if (this.selectedCategory) {
        result = result.filter(s => s.category === this.selectedCategory);
      }
      
      return result.sort((a, b) => a.name.localeCompare(b.name));
    },
    
    get uniqueCategories() {
      return [...new Set(this.skills.map(s => s.category))];
    },
    
    selectCategory(category) {
      this.selectedCategory = this.selectedCategory === category ? null : category;
    },
    
    async loadSkills() {
      try {
        const response = await fetch('/api/skills');
        this.skills = await response.json();
      } catch (error) {
        console.error('Failed to load skills:', error);
      }
    }
  }));
});
