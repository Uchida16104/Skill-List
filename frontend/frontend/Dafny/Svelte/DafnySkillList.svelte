<script>
  // Generated from Dafny Svelte verification
  import { SkillListDafny } from '../JS/SkillListDafny.js';
  
  export let skills = [];
  let searchQuery = "";
  let selectedCategory = null;
  
  $: uniqueCategories = SkillListDafny.getUniqueCategories(skills);
  $: filteredSkills = getFilteredSkills();
  
  function getFilteredSkills() {
    let result = skills;
    if (searchQuery) {
      result = result.filter(s => 
        s.name.toLowerCase().includes(searchQuery.toLowerCase())
      );
    }
    if (selectedCategory) {
      result = SkillListDafny.filterByCategory(result, selectedCategory);
    }
    return SkillListDafny.sortSkillsByName(result);
  }
</script>

<div class="dafny-skill-list">
  <div class="controls">
    <input 
      type="text" 
      bind:value={searchQuery}
      placeholder="Search skills..."
      class="search-input"
    />
    <div class="categories">
      {#each uniqueCategories as category}
        <button
          class:active={selectedCategory === category}
          on:click={() => selectedCategory = selectedCategory === category ? null : category}
        >
          {category}
        </button>
      {/each}
    </div>
  </div>
  
  <div class="skills-grid">
    {#each filteredSkills as skill (skill.id)}
      <div class="dafny-skill-card">
        <h3>{skill.name}</h3>
        <p class="category">{skill.category}</p>
        <p class="level">Level: {skill.level}/5</p>
        {#if skill.verified}
          <span class="dafny-verified">✓ Verified</span>
        {/if}
      </div>
    {/each}
  </div>
</div>
