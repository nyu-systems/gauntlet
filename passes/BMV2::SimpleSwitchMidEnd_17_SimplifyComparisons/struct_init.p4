--- dumps/p4_16_samples/struct_init.p4/pruned/struct_init-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:32:17.596010200 +0200
+++ dumps/p4_16_samples/struct_init.p4/pruned/struct_init-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:32:17.598235600 +0200
@@ -6,7 +6,7 @@ struct metadata_t {
 }
 control I(inout metadata_t meta) {
     apply {
-        if (meta.foo == { 9w192 }) 
+        if (true && meta.foo._v == 9w192) 
             meta.foo._v = meta.foo._v + 9w1;
     }
 }
