# Supplement Material

## Dependencies

- `agda` version `2.7.0.1`: https://agda.readthedocs.io/en/v2.7.0.1/getting-started/installation.html
- `standard-library` version `2.1.1`: https://github.com/agda/agda-stdlib/blob/v2.1-release/doc/installation-guide.md

## Structure

### External Code

- `Ordinal.agda`: 
- `Universe.agda`: 

### Library Code

- `ExtendedHierarchy.agda`: 
- `BoundQuantification.agda`: 

### Stratified System F Formalizations

- `SSF.agda`: 
- `SSF-UP.agda`:
- `SSF-UP-IR.agda`:
- `SSF-UP-EH.agda`:

#### Comparison Matrices 

##### Glossary 

| Code | Description |
|-----|--------------------------|
| SSF | Stratified System F      |
| UP  | Universe Polymorphism    |
| EH  | Extended Level Hierarchy |
| IR  | Induction Recursion      |

##### Object Language

| Name       | Universe Hierarchy | Universe Polymorphism |
|------------|--------------------|-----------------------|
| SSF        | yes                | no                    |
| SSF-UP     | yes                | yes                   |
| SSF-UP-EH  | yes                | yes                   |
| SSF-UP-IR  | yes                | yes                   |

##### Formalization Methods

| Name       | Level Magic | Induction Recursion | Extended Level Hierarchy |
|------------|-------------|---------------------|--------------------------|
| SSF        | yes         | no                  | no                       |
| SSF-UP     | no          | no                  | no                       |
| SSF-UP-EH  | yes (*)     | no                  | yes                      | 
| SSF-UP-IR  | no          | yes                 | no                       |


##### Problems 

| Name       | Suffers Subst Hell Unnecessarily | Hits Hierarchy Limit |
|------------|--------------------|----------------------|
| SSF        | no                 | no                   |
| SSF-UP     | yes                | yes                  |
| SSF-UP-EH  | no (*)             | no                   |
| SSF-UP-IR  | yes                | no                   |