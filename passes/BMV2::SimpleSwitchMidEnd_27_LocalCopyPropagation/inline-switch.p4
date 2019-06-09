--- before_pass
+++ after_pass
@@ -1,5 +1,4 @@
 control d(out bit<32> x) {
-    bool cinst_hasReturned;
     @name("d.cinst.a1") action cinst_a1_0() {
     }
     @name("d.cinst.a2") action cinst_a2_0() {
@@ -13,14 +12,11 @@ control d(out bit<32> x) {
     }
     apply {
         {
-            cinst_hasReturned = false;
             switch (cinst_t.apply().action_run) {
                 cinst_a1_0: 
                 cinst_a2_0: {
-                    cinst_hasReturned = true;
                 }
                 default: {
-                    cinst_hasReturned = true;
                 }
             }
         }
