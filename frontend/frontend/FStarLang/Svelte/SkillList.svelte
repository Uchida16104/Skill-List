<script>
  // Generated from F* Svelte verification
  export let skills = [];
  export let selectedCategory = null;
  export let searchQuery = "";
  
  $: filteredSkills = skills
    .filter(s => !searchQuery || s.name.toLowerCase().includes(searchQuery.toLowerCase()))
    .filter(s => !selectedCategory || s.category === selectedCategory);
  
  function updateSearch(event) {
    searchQuery = event.target.value;
  }
  
  function selectCategory(category) {
    selectedCategory = selectedCategory === category ? null : category;
  }
</script>

<div class="skill-list-component">
  <input 
    type="text" 
    placeholder="Search skills..." 
    on:input={updateSearch}
    class="search-input"
  />
  
  <div class="skill-grid">
    {#each filteredSkills as skill}
      <div class="skill-card">
        <h3>{skill.name}</h3>
        <p class="category">{skill.category}</p>
        {#if skill.verified}
          <span class="verified-badge">✓ Verified</span>
        {/if}
      </div>
    {/each}
  </div>
</div>

<style>
  .skill-list-component { padding: 20px; }
  .search-input { width: 100%; padding: 12px; margin-bottom: 20px; }
  .skill-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(300px, 1fr)); gap: 16px; }
</style>
