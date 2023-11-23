component Application provides App {
  def main() : int {

	var a:int; 
	a=0;
	
	//basic
	a+=2;
	print(a); //2
	
	//reference
	var ref:&int;
	ref=&a;
	ref+=2;
	print(a); //4
	
	//array
	var arr:int[3];
	arr[0]=5;
	arr[1]=10;
	arr[2]=15;
	var index:int;
	index=0;	
	arr[++index]+=1;
	print(arr[0]); //5
	print(arr[1]); //11
	print(arr[2]); //15
	
    return 0;
  }
}  
