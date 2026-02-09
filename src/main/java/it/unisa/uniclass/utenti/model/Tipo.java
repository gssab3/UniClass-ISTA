package it.unisa.uniclass.utenti.model;

/**
 * Enumera i tipi di utenti che possono essere presenti nel sistema UniClass.
 * <p>
 * I tipi disponibili sono:
 * <ul>
 *   <li>{@link Accademico} - Rappresenta un accademico, che può essere uno studente, docente o coordinatore.</li>
 *   <li>{@link #PersonaleTA} - Rappresenta il personale tecnico-amministrativo.</li>
 * </ul>
 * </p>
 */
public enum Tipo {
    /**
     * Rappresenta uno Accademico.
     */
    Accademico,
    /**
     * Rappresenta il personale tecnico-amministrativo.
     */
    PersonaleTA
}
