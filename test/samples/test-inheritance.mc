interface A extends B,C{
	var a:int;
	def add_ten(n:&int);
}
interface B{
	var b:int;
}
interface C extends D{
	var c:int;
}
interface D{
	var d:int;
}

component Prova provides A{
	var a:int;
	var b:int;
	var c:int;
	var d:int;

	def add_ten(n:&int){
	  n+=10;
	}
}

component EntryPoint provides App uses A { 

  def main() : int {
  	a=2;
  	add_ten(&a); 
  	print(a);//12
  	d=7;
  	print(d); //7

    return 0;
  }
}



connect EntryPoint.A <- Prova.A
