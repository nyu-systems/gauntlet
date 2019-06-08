--- before_pass
+++ after_pass
@@ -1,5 +1,4 @@
 control d(out bit<32> x) {
-    bool cinst_hasReturned_0;
     @name("d.cinst.a1") action cinst_a1() {
     }
     @name("d.cinst.a2") action cinst_a2() {
@@ -13,14 +12,11 @@ control d(out bit<32> x) {
     }
     apply {
         {
-            cinst_hasReturned_0 = false;
             switch (cinst_t_0.apply().action_run) {
                 cinst_a1: 
                 cinst_a2: {
-                    cinst_hasReturned_0 = true;
                 }
                 default: {
-                    cinst_hasReturned_0 = true;
                 }
             }
         }
