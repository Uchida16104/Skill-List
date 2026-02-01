# Generated from F* Analysis verification
from typing import List, Optional, Dict
from dataclasses import dataclass

@dataclass
class DataPoint:
    timestamp: int
    value: int
    category: str

def calculate_sum(values: List[int]) -> int:
    """Verified sum calculation"""
    return sum(values)

def calculate_average(values: List[int]) -> Optional[int]:
    """Verified average calculation"""
    if not values:
        return None
    return sum(values) // len(values)

def find_maximum(values: List[int]) -> Optional[int]:
    """Verified maximum finding"""
    if not values:
        return None
    return max(values)

def find_minimum(values: List[int]) -> Optional[int]:
    """Verified minimum finding"""
    if not values:
        return None
    return min(values)

def filter_by_threshold(values: List[int], threshold: int) -> List[int]:
    """Verified threshold filtering"""
    return [v for v in values if v >= threshold]

def group_by_category(data: List[DataPoint], category: str) -> List[DataPoint]:
    """Verified category grouping"""
    return [d for d in data if d.category == category]

def calculate_statistics(values: List[int]) -> Dict[str, Optional[int]]:
    """Calculate comprehensive statistics"""
    return {
        'sum': calculate_sum(values) if values else None,
        'average': calculate_average(values),
        'maximum': find_maximum(values),
        'minimum': find_minimum(values),
        'count': len(values)
    }
