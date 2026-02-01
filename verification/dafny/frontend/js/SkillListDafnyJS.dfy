// Dafny source file for verified JavaScript frontend components
// This file will compile to JavaScript for use in Next.js

module SkillListDafnyJS {

  // Verified data structures for skill management
  datatype Skill = Skill(
    id: nat,
    name: string,
    category: string,
    level: nat,
    verified: bool
  )

  // Verified predicate for valid skill level
  predicate ValidSkillLevel(level: nat)
  {
    1 <= level <= 5
  }

  // Verified predicate for valid skill
  predicate ValidSkill(s: Skill)
  {
    |s.name| > 0 &&
    |s.name| <= 100 &&
    |s.category| > 0 &&
    ValidSkillLevel(s.level)
  }

  // Verified method to filter skills by category
  method FilterByCategory(skills: seq<Skill>, category: string) returns (filtered: seq<Skill>)
    ensures forall i :: 0 <= i < |filtered| ==> filtered[i].category == category
    ensures forall s :: s in filtered ==> s in skills
  {
    filtered := [];
    var i := 0;
    while i < |skills|
      invariant 0 <= i <= |skills|
      invariant forall j :: 0 <= j < |filtered| ==> filtered[j].category == category
    {
      if skills[i].category == category {
        filtered := filtered + [skills[i]];
      }
      i := i + 1;
    }
  }

  // Verified method to count verified skills
  method CountVerified(skills: seq<Skill>) returns (count: nat)
    ensures count <= |skills|
    ensures count == |set i | 0 <= i < |skills| && skills[i].verified|
  {
    count := 0;
    var i := 0;
    while i < |skills|
      invariant 0 <= i <= |skills|
      invariant count == |set j | 0 <= j < i && skills[j].verified|
    {
      if skills[i].verified {
        count := count + 1;
      }
      i := i + 1;
    }
  }

  // Verified method to find skill by ID
  method FindSkillById(skills: seq<Skill>, targetId: nat) returns (result: Option<Skill>)
    ensures result.Some? ==> result.value in skills && result.value.id == targetId
    ensures result.None? ==> forall s :: s in skills ==> s.id != targetId
  {
    var i := 0;
    while i < |skills|
      invariant 0 <= i <= |skills|
      invariant forall j :: 0 <= j < i ==> skills[j].id != targetId
    {
      if skills[i].id == targetId {
        return Some(skills[i]);
      }
      i := i + 1;
    }
    return None;
  }

  // Verified method to validate skill name
  method IsValidSkillName(name: string) returns (valid: bool)
    ensures valid <==> |name| > 0 && |name| <= 100
  {
    valid := |name| > 0 && |name| <= 100;
  }

  // Verified method to sort skills by name (insertion sort)
  method SortSkillsByName(skills: seq<Skill>) returns (sorted: seq<Skill>)
    ensures |sorted| == |skills|
    ensures forall s :: s in skills ==> s in sorted
    ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i].name <= sorted[j].name
  {
    sorted := [];
    var i := 0;
    while i < |skills|
      invariant 0 <= i <= |skills|
      invariant |sorted| == i
      invariant forall s :: s in sorted ==> s in skills
      invariant forall j, k :: 0 <= j < k < |sorted| ==> sorted[j].name <= sorted[k].name
    {
      sorted := InsertSorted(sorted, skills[i]);
      i := i + 1;
    }
  }

  // Helper method for insertion sort
  method InsertSorted(sorted: seq<Skill>, skill: Skill) returns (result: seq<Skill>)
    requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i].name <= sorted[j].name
    ensures |result| == |sorted| + 1
    ensures skill in result
    ensures forall s :: s in sorted ==> s in result
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i].name <= result[j].name
  {
    var i := 0;
    while i < |sorted| && sorted[i].name <= skill.name
      invariant 0 <= i <= |sorted|
    {
      i := i + 1;
    }
    result := sorted[..i] + [skill] + sorted[i..];
  }

  // Verified method to calculate total skill level
  method CalculateTotalLevel(skills: seq<Skill>) returns (total: nat)
    ensures total >= 0
  {
    total := 0;
    var i := 0;
    while i < |skills|
      invariant 0 <= i <= |skills|
      invariant total >= 0
    {
      total := total + skills[i].level;
      i := i + 1;
    }
  }

  // Verified method to get unique categories
  method GetUniqueCategories(skills: seq<Skill>) returns (categories: seq<string>)
    ensures forall c :: c in categories ==> exists s :: s in skills && s.category == c
    ensures forall s :: s in skills ==> s.category in categories
  {
    categories := [];
    var i := 0;
    while i < |skills|
      invariant 0 <= i <= |skills|
      invariant forall c :: c in categories ==> exists j :: 0 <= j < i && skills[j].category == c
    {
      if skills[i].category !in categories {
        categories := categories + [skills[i].category];
      }
      i := i + 1;
    }
  }

  datatype Option<T> = None | Some(value: T)
}
