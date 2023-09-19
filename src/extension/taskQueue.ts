class Queue {
    private _items: any[];

    constructor() { 
        this._items = []; 
    }
    
    enqueue(item: any) { 
        this._items.push(item); 
    }
    dequeue() { 
        return this._items.shift(); 
    }
    
    get size() { 
        return this._items.length; 
    }
}

export class AutoQueue extends Queue {
    private _pendingPromise: boolean;

    constructor() {
      super();
      this._pendingPromise = false;
    }
  
    enqueue(action: any): Promise<any> {
        return new Promise((resolve, reject) => {
            super.enqueue({ action, resolve, reject });
            this.dequeue();
        });
    }
  
    /**
	 * Remove element from the queue by either resolving its Promise or running its fn async
	 * Runtime: O(1)
	 * @returns {boolean} true if queue is empty
	 */
    async dequeue(): Promise<boolean> {
        if (this._pendingPromise) {
            return false;
        }
  
        let item = super.dequeue();
    
        if (!item) {
            return false;
        }
  
        try {
            this._pendingPromise = true;  
            let payload = await item.action(this);

            this._pendingPromise = false;
            item.resolve(payload);
        } catch (e) {
            this._pendingPromise = false;
            item.reject(e);
        } finally {
            this.dequeue();
        }
  
        return true;
    }
}