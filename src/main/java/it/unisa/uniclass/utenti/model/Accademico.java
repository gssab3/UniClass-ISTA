package it.unisa.uniclass.utenti.model;

import jakarta.persistence.*;
import java.time.LocalDate;
import java.util.List;

@Entity
@Table(name = "accademico")
@PrimaryKeyJoinColumn(name = "utente_email") // Collega la PK di Accademico alla PK di Utente
@NamedQueries({
        @NamedQuery(name = "Accademico.findAll", query = "SELECT a FROM Accademico a"),
        @NamedQuery(name = "Accademico.findByMatricola", query = "SELECT a FROM Accademico a WHERE a.matricola = :matricola"),
        @NamedQuery(name = "Accademico.findByRuolo", query = "SELECT a FROM Accademico a WHERE a.ruolo = :ruolo"),
        @NamedQuery(name = "Accademico.findByRuoloAndDip", query = "SELECT a FROM Accademico a WHERE a.ruolo = :ruolo AND a.dipartimento = :dipartimento")
})
public class Accademico extends Utente {

    private static final long serialVersionUID = 1L;

    @Column(name = "matricola", unique = true)
    private String matricola;

    @Enumerated(EnumType.STRING)
    @Column(name = "ruolo", nullable = false)
    private Ruolo ruolo; // STUDENTE, DOCENTE, COORDINATORE

    @Column(name = "dipartimento")
    private String dipartimento;

    @Column(name = "corso_laurea")
    private String corsoLaurea;

    @Column(name = "attivato")
    private boolean attivato;

    // Relazioni (adattate dal tuo schema "Corsi", "Messaggi", ecc.)
    // Esempio: Un accademico può seguire o tenere molti corsi
    // Verifica il nome della variabile nel lato "Many" (es. in Corso.java)
    /* @OneToMany(mappedBy = "accademico")
    private List<Corso> corsi;
    */

    public Accademico() {
        super();
    }

    public Accademico(String email, String password, String nome, String cognome, LocalDate dataNascita, String telefono,
                      String matricola, Ruolo ruolo, String dipartimento) {
        super(email, password, nome, cognome, dataNascita, telefono);
        this.matricola = matricola;
        this.ruolo = ruolo;
        this.dipartimento = dipartimento;
        this.attivato = false; // Default a false se richiede attivazione
    }

    // --- Getter e Setter ---

    public String getMatricola() { return matricola; }
    public void setMatricola(String matricola) { this.matricola = matricola; }

    public Ruolo getRuolo() { return ruolo; }
    public void setRuolo(Ruolo ruolo) { this.ruolo = ruolo; }

    public String getDipartimento() { return dipartimento; }
    public void setDipartimento(String dipartimento) { this.dipartimento = dipartimento; }

    public String getCorsoLaurea() { return corsoLaurea; }
    public void setCorsoLaurea(String corsoLaurea) { this.corsoLaurea = corsoLaurea; }

    public boolean isAttivato() { return attivato; }
    public void setAttivato(boolean attivato) { this.attivato = attivato; }
}