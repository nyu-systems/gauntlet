--- before_pass
+++ after_pass
@@ -9,13 +9,7 @@ extern Random2 {
 parser caller() {
     @name("caller.rand1") Random2() rand1_0;
     state start {
-        transition callee_start;
-    }
-    state callee_start {
         rand1_0.read();
-        transition start_0;
-    }
-    state start_0 {
         transition accept;
     }
 }
