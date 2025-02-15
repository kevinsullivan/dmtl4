# Semantic Domain: Boolean Algebra

<!-- toc -->

```lean
namespace DMT1.Lectures.theoryExtensions.domain

def imp : Bool → Bool → Bool
| true, true => true
| true, false => false
| false, true => true
| false, false => true

def iff : Bool → Bool → Bool
| true, true => true
| false, false => true
| _, _ => false

end DMT1.Lectures.theoryExtensions.domain
```
