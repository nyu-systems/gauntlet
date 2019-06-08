--- dumps/pruned/struct_init-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:34:06.668595800 +0200
+++ dumps/pruned/struct_init-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:34:06.676267700 +0200
@@ -6,7 +6,7 @@ struct metadata_t {
 }
 control I(inout metadata_t meta) {
     apply {
-        if (meta.foo == { 9w192 }) 
+        if (true && meta.foo._v == 9w192) 
             meta.foo._v = meta.foo._v + 9w1;
     }
 }
