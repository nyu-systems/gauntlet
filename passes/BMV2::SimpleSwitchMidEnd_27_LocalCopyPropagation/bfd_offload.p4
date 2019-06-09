--- before_pass
+++ after_pass
@@ -11,15 +11,11 @@ BFD_Offload(16w32768) bfd_session_livene
     }
     bool on_tx(in bit<16> index) {
         bit<8> tmp;
-        bit<8> tmp_0;
-        bit<8> c_0;
         tmp = this.getTx(index);
-        tmp_0 = tmp + 8w1;
-        c_0 = tmp_0;
-        if (c_0 >= 8w4) 
+        if (tmp + 8w1 >= 8w4) 
             return true;
         else {
-            this.setTx(index, c_0);
+            this.setTx(index, tmp + 8w1);
             return false;
         }
     }
