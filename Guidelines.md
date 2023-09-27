Following are guidelines that one should follow unless there is a good technical reason not to.

* Languages features to avoid:
    * import opened
    * subset types
    * covariance and contraviance
    
* Even if a function is not meant to be part of the compiled code, you should not use ghost unless necessary
* Do not attach postconditions to functions. Instead, prove the postcondition as a separate lemma.
* Name preconditions of lemmas and reveal them only when necessary
* Unless necessary

Prefer 

lemma Foo(x:nat)
  ensues P(x)

to

lemma Foo()
  ensures forall x: nat :: P(x)

Prefer

lemma Foo()
  requires A
  ensures B

to 

lemma Foo()
  ensures A ==> B


