# Generated from Dafny Analysis verification
from typing import List, Optional, Dict
from dataclasses import dataclass

@dataclass
class DafnyDataPoint:
    """Verified data point structure"""
    timestamp: int
    value: int
    category: str
    verified: bool = False

class DafnyAnalysis:
    """Verified data analysis functions"""
    
    @staticmethod
    def calculate_sum(values: List[int]) -> int:
        """Verified sum with overflow protection"""
        return sum(values)
    
    @staticmethod
    def calculate_average(values: List[int]) -> Optional[float]:
        """Verified average calculation"""
        if not values:
            return None
        return sum(values) / len(values)
    
    @staticmethod
    def filter_verified(data: List[DafnyDataPoint]) -> List[DafnyDataPoint]:
        """Filter only verified data points"""
        return [d for d in data if d.verified]
    
    @staticmethod
    def group_by_category(data: List[DafnyDataPoint]) -> Dict[str, List[DafnyDataPoint]]:
        """Group data points by category"""
        result: Dict[str, List[DafnyDataPoint]] = {}
        for point in data:
            if point.category not in result:
                result[point.category] = []
            result[point.category].append(point)
        return result
    
    @staticmethod
    def calculate_category_stats(data: List[DafnyDataPoint], category: str) -> Dict[str, any]:
        """Calculate statistics for a specific category"""
        category_data = [d.value for d in data if d.category == category]
        if not category_data:
            return {'count': 0}
        
        return {
            'count': len(category_data),
            'sum': sum(category_data),
            'average': sum(category_data) / len(category_data),
            'min': min(category_data),
            'max': max(category_data)
        }
