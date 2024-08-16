# Java Garbage Collector

## CS6004: Code Optimization for Object-Oriented Languages

**by**

Aditya Hiteshbhai Kansara (23M0748)

**Under the guidance of**

Prof. Manas Thakur

Department of Computer Science and Engineering  
Indian Institute of Technology, Bombay  
Mumbai 400-076

---

## Overview

This project involves implementing a static analysis tool using the Soot framework to analyze Java bytecode. The objective is to perform whole-program analysis, detect issues such as dead code, and incorporate a Java Garbage Collector as part of the analysis.

### Objectives

- Implement a static analysis tool with Soot for analyzing Java bytecode.
- Detect dead code and perform whole-program analysis.
- Integrate a Java Garbage Collector to identify and remove unreachable objects.

## File Analysis

### `AnalysisTransformer.java`

**Purpose:**  
Responsible for transforming the program's "scene" and conducting the analysis, focusing on call graphs and detecting unused or dead code.

**Components:**
- **CallGraph (cg):** Holds the call graph for the analyzed program to track method invocations.
- **TreeMap Structure:** Nested `TreeMap` structures (Answer and Dead) store results of the analysis, including identifying dead code.
- **Pair Class:** A custom generic `Pair` class used for storing analysis data, hinting at context-sensitive analysis.
- **Garbage Collector Implementation:** Integrates garbage collection logic to identify and handle unreachable objects. The collector traverses data flow and call graphs to determine unreferenced objects.

### `PA3.java`

**Purpose:**  
Serves as the entry point to the analysis, setting up the Soot framework and defining the analysis configuration.

**Components:**
- **Soot Configuration:** Configures Soot for whole-program analysis, Jimple output, and line number preservation. Options include specifying the classpath, main class, and directories.
- **Garbage Collection Trigger:** The garbage collector is triggered as part of the analysis. It removes unnecessary objects after call graph analysis and dead code detection, simulating Java's runtime garbage collector behavior.

## Garbage Collector Implementation

**Objective:**  
Focuses on detecting unreachable objects in the analyzed code. Simulates Java's garbage collection within the static analysis context.

**Steps:**
1. **Object Tracking:** Objects and variables are tracked using data structures like `TreeMap`.
2. **Reachability Analysis:** Performs reachability analysis by traversing the call graph and control flow to determine if an object is still accessible.
3. **Garbage Collection:** Identifies unreachable objects and removes them from memory or excludes them from further analysis.

## Conclusion

This project integrates static analysis with garbage collection to enhance memory management during the analysis. The Soot framework is used for bytecode analysis, while the garbage collector ensures efficient memory usage by identifying and removing unused objects. 

- **`AnalysisTransformer.java`** handles core logic and garbage collection.
- **`PA3.java`** sets up the environment and triggers the analysis.

For more details, please refer to the provided code files and the Git repository.

