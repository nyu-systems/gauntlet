--- before_pass
+++ after_pass
@@ -1,4 +1,5 @@
 control d(out bit<32> x) {
+    bool cinst_hasReturned_0;
     @name("d.cinst.a1") action cinst_a1() {
     }
     @name("d.cinst.a2") action cinst_a2() {
@@ -12,7 +13,7 @@ control d(out bit<32> x) {
     }
     apply {
         {
-            bool cinst_hasReturned_0 = false;
+            cinst_hasReturned_0 = false;
             switch (cinst_t_0.apply().action_run) {
                 cinst_a1: 
                 cinst_a2: {
