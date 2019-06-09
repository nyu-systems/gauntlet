--- before_pass
+++ after_pass
@@ -26,7 +26,7 @@ control c(inout bit<1> r) {
             }
         }
         f<tuple_0>({ s_f1_field, s_f1_field_0 });
-        r = 1w0 & 1w1;
+        r = 1w0;
     }
 }
 control simple(inout bit<1> r);
