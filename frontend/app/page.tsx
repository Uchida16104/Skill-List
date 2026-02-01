'use client';

import { useEffect, useState } from 'react';
import '../frontend/FStarLang/CSS/skilllist.css';
import '../frontend/Dafny/CSS/dafny-styles.css';

interface Skill {
  id: number;
  name: string;
  category: string;
  level: number;
  verified: boolean;
  created_at: string;
}

export default function Home() {
  const [skills, setSkills] = useState<Skill[]>([]);
  const [loading, setLoading] = useState(true);
  const [searchQuery, setSearchQuery] = useState('');
  const [selectedCategory, setSelectedCategory] = useState<string | null>(null);
  const [categories, setCategories] = useState<string[]>([]);
  
  const API_URL = process.env.NEXT_PUBLIC_API_URL || 'http://localhost:10000';
  
  useEffect(() => {
    loadSkills();
    loadCategories();
  }, []);
  
  const loadSkills = async () => {
    try {
      const response = await fetch(`${API_URL}/api/skills`);
      const data = await response.json();
      setSkills(data);
    } catch (error) {
      console.error('Failed to load skills:', error);
    } finally {
      setLoading(false);
    }
  };
  
  const loadCategories = async () => {
    try {
      const response = await fetch(`${API_URL}/api/categories`);
      const data = await response.json();
      setCategories(data);
    } catch (error) {
      console.error('Failed to load categories:', error);
    }
  };
  
  const filteredSkills = skills
    .filter(s => !searchQuery || s.name.toLowerCase().includes(searchQuery.toLowerCase()))
    .filter(s => !selectedCategory || s.category === selectedCategory);
  
  return (
    <main className="min-h-screen bg-gray-50 p-8">
      <div className="max-w-7xl mx-auto">
        <header className="mb-8">
          <h1 className="text-4xl font-bold text-gray-900 mb-2">
            Skill List Portfolio
          </h1>
          <p className="text-gray-600">
            Formally verified with F* and Dafny
          </p>
        </header>
        
        <div className="mb-6 space-y-4">
          <input
            type="text"
            placeholder="Search skills..."
            value={searchQuery}
            onChange={(e) => setSearchQuery(e.target.value)}
            className="w-full px-4 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-transparent"
          />
          
          <div className="flex flex-wrap gap-2">
            {categories.map(category => (
              <button
                key={category}
                onClick={() => setSelectedCategory(selectedCategory === category ? null : category)}
                className={`px-4 py-2 rounded-lg transition-colors ${
                  selectedCategory === category
                    ? 'bg-blue-600 text-white'
                    : 'bg-white text-gray-700 border border-gray-300 hover:bg-gray-50'
                }`}
              >
                {category}
              </button>
            ))}
          </div>
        </div>
        
        {loading ? (
          <div className="text-center py-12">
            <div className="inline-block animate-spin rounded-full h-12 w-12 border-b-2 border-blue-600"></div>
            <p className="mt-4 text-gray-600">Loading skills...</p>
          </div>
        ) : (
          <div className="skill-list-container">
            {filteredSkills.map(skill => (
              <div key={skill.id} className="skill-card dafny-skill-card">
                <h3 className="text-xl font-semibold text-gray-900 mb-2">
                  {skill.name}
                </h3>
                <p className="text-gray-600 mb-2">{skill.category}</p>
                <div className="flex items-center justify-between">
                  <span className="text-sm text-gray-500">
                    Level: {skill.level}/5
                  </span>
                  {skill.verified && (
                    <span className="verified-badge dafny-verified">
                      ✓ Verified
                    </span>
                  )}
                </div>
              </div>
            ))}
          </div>
        )}
        
        {!loading && filteredSkills.length === 0 && (
          <div className="text-center py-12">
            <p className="text-gray-600">No skills found matching your criteria.</p>
          </div>
        )}
        
        <footer className="mt-12 text-center text-gray-500 text-sm">
          <p>Built with formally verified F* and Dafny components</p>
          <p>Backend: Rust on Render | Frontend: Next.js on Vercel</p>
        </footer>
      </div>
    </main>
  );
}
