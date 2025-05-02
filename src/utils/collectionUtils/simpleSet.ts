export class SimpleSet<EntityType, KeyType> {
    private readonly entities: Map<KeyType, boolean> = new Map();

    constructor(
        private readonly keyExtractor: (entity: EntityType) => KeyType
    ) {}

    add(entity: EntityType) {
        this.entities.set(this.keyExtractor(entity), true);
    }

    has(entity: EntityType): boolean {
        return this.entities.has(this.keyExtractor(entity));
    }
}
