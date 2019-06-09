--- before_pass
+++ after_pass
@@ -33,7 +33,6 @@ struct h {
 struct m {
 }
 parser MyParser(packet_in b, out h hdr, inout m meta, inout standard_metadata_t std) {
-    bit<16> l3_etherType;
     state start {
         hdr.ether.setInvalid();
         hdr.vlan.setInvalid();
@@ -43,8 +42,7 @@ parser MyParser(packet_in b, out h hdr,
         transition L3_start;
     }
     state L3_start {
-        l3_etherType = hdr.ether.etherType;
-        transition select(l3_etherType) {
+        transition select(hdr.ether.etherType) {
             16w0x800: L3_ipv4;
             16w0x8100: L3_vlan;
             default: start_2;
