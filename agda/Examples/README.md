
# Examples

# Comparison Matrices 

## Glossary 


| Code | Description |
|-----|--------------------------|
| SSF | Stratified System F      |
| UP  | Universe Polymorphism    |
| ELH | Extended Level Hierarchy |
| IR  | Induction Recursion      |

## Object Language

| Name       | Universe Hierarchy | Universe Polymorphism |
|------------|--------------------|-----------------------|
| SSF        | yes                | no                    |
| SSF-UP     | yes                | yes                   |
| SSF-UP-ELH | yes                | yes                   |
| SSF-UP-IR  | yes                | yes                   |

## Formalization Methods

| Name       | Level Magic | Induction Recursion | Extended Level Hierarchy |
|------------|-------------|---------------------|--------------------------|
| SSF        | yes         | no                  | no                       |
| SSF-UP     | no          | no                  | no                       |
| SSF-UP-ELH | yes (*)     | no                  | yes                      | 
| SSF-UP-IR  | no          | yes                 | no                       |


## Problems 

| Name       | Suffers Subst Hell | Hits Hierarchy Limit |
|------------|--------------------|----------------------|
| SSF        | no                 | yes                  |
| SSF-UP     | yes                | yes                  |
| SSF-UP-ELH | no (*)             | no                   |
| SSF-UP-IR  | yes                | no                   |