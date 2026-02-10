package it.unisa.uniclass.common.config.database;

import it.unisa.uniclass.common.security.CredentialSecurity;
import it.unisa.uniclass.orari.model.*;
import it.unisa.uniclass.utenti.model.*;
import jakarta.annotation.PostConstruct;
import jakarta.ejb.Singleton;
import jakarta.ejb.Startup;
import jakarta.persistence.EntityManager;
import jakarta.persistence.PersistenceContext;

import java.sql.Time;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

@Singleton
@Startup
public class DatabasePopulator {

    @PersistenceContext(unitName = "DBUniClassPU")
    private EntityManager em;

    @PostConstruct
    public void populateDB() {
        // --- 1. Creazione Utenti (Docenti) ---
        // Sostituisco new Docente() con new Accademico() + Ruolo.DOCENTE

        Accademico docente1 = creaAccademico("prof1@unisa.it", "password", "Mario", "Rossi", "0123456789", "D001", Ruolo.Docente, "Informatica");
        Accademico docente2 = creaAccademico("prof2@unisa.it", "password", "Luigi", "Verdi", "0123456788", "D002", Ruolo.Docente, "Matematica");
        Accademico docente3 = creaAccademico("prof3@unisa.it", "password", "Anna", "Bianchi", "0123456787", "D003", Ruolo.Docente, "Fisica");

        // --- 2. Creazione Utenti (Studenti) ---
        // Sostituisco new Studente() con new Accademico() + Ruolo.STUDENTE

        Accademico studente1 = creaAccademico("stud1@studenti.unisa.it", "password", "Luca", "Neri", "3334445556", "0512100001", Ruolo.Studente, "Informatica");
        Accademico studente2 = creaAccademico("stud2@studenti.unisa.it", "password", "Marco", "Gialli", "3334445557", "0512100002", Ruolo.Studente, "Informatica");

        // --- 3. Creazione Personale TA (Utente Generico) ---
        // Sostituisco new PersonaleTA() con new Utente() + Tipo appropriato

        Utente ta1 = new Utente(
                "admin@unisa.it",
                CredentialSecurity.hashPassword("password"),
                "Admin",
                "User",
                LocalDate.of(1980, 1, 1),
                "089123456",
                LocalDate.now(),
                Tipo.PersonaleTA // Assicurati che l'Enum Tipo abbia questo valore, o usa un altro valore generico
        );
        em.persist(ta1);


        // --- 4. Creazione Anni Didattici ---
        AnnoDidattico anno1 = new AnnoDidattico("Anno 1");
        AnnoDidattico anno2 = new AnnoDidattico("Anno 2");
        AnnoDidattico anno3 = new AnnoDidattico("Anno 3");
        em.persist(anno1);
        em.persist(anno2);
        em.persist(anno3);

        // --- 5. Creazione Corsi di Laurea ---
        CorsoLaurea cl = new CorsoLaurea("Ingegneria Informatica");
        // Associazione Anni a Corso Laurea
        List<AnnoDidattico> anniCL = new ArrayList<>();
        anniCL.add(anno1);
        anniCL.add(anno2);
        anniCL.add(anno3);
        cl.setAnniDidattici(anniCL);
        em.persist(cl);

        // Associazione Studenti a Corso Laurea
        studente1.setCorsoLaurea(cl);
        studente2.setCorsoLaurea(cl);
        em.merge(studente1);
        em.merge(studente2);

        // --- 6. Creazione Resti ---
        Resto resto1 = new Resto("Resto 0", cl);
        Resto resto2 = new Resto("Resto 1", cl);
        em.persist(resto1);
        em.persist(resto2);

        // --- 7. Creazione Corsi e Associazione Docenti ---

        // Corso 1
        Corso corso1 = new Corso("Programmazione 1");
        corso1.setAnnoDidattico(anno1);
        corso1.setCorsoLaurea(cl);

        // Fix: uso getAccademici invece di getDocenti
        corso1.getAccademici().add(docente1);
        docente1.getCorsi().add(corso1);
        em.persist(corso1);

        // Corso 2
        Corso corso2 = new Corso("Analisi 1");
        corso2.setAnnoDidattico(anno1);
        corso2.setCorsoLaurea(cl);
        corso2.getAccademici().add(docente2);
        docente2.getCorsi().add(corso2);
        em.persist(corso2);

        // Corso 3
        Corso corso3 = new Corso("Fisica 1");
        corso3.setAnnoDidattico(anno1);
        corso3.setCorsoLaurea(cl);
        corso3.getAccademici().add(docente3);
        docente3.getCorsi().add(corso3);
        em.persist(corso3);

        // Persistiamo aggiornamenti docenti
        em.merge(docente1);
        em.merge(docente2);
        em.merge(docente3);

        // --- 8. Creazione Aule ---
        Aula aula1 = new Aula(0, "F3", "P1");
        Aula aula2 = new Aula(0, "F3", "P2");
        em.persist(aula1);
        em.persist(aula2);

        // --- 9. Creazione Lezioni ---
        // Esempio creazione lezione
        Lezione lezione1 = new Lezione(
                1,
                Time.valueOf("09:00:00"),
                Time.valueOf("11:00:00"),
                Giorno.LUNEDI,
                resto1,
                corso1,
                aula1
        );
        // Associazione docente-lezione (Fix: getAccademici)
        lezione1.getAccademici().add(docente1);
        docente1.getLezioni().add(lezione1);

        em.persist(lezione1);
        em.merge(docente1);

        System.out.println("Database Popolato con successo (Refactored)!");
    }

    /**
     * Helper per creare e persistere un Accademico
     */
    private Accademico creaAccademico(String email, String pass, String nome, String cognome, String tel, String matricola, Ruolo ruolo, String dip) {
        Accademico a = new Accademico();
        a.setEmail(email);
        a.setPassword(CredentialSecurity.hashPassword(pass));
        a.setNome(nome);
        a.setCognome(cognome);
        a.setDataNascita(LocalDate.of(1990, 1, 1));
        a.setTelefono(tel);
        a.setIscrizione(LocalDate.now());

        // Mappatura Tipo per compatibilità legacy (se Tipo esiste ancora in Utente)
        if (ruolo == Ruolo.Studente) a.setTipo(Tipo.Accademico);
        else if (ruolo == Ruolo.Docente) a.setTipo(Tipo.Accademico);
        else if (ruolo == Ruolo.Coordinatore) a.setTipo(Tipo.Accademico);

        a.setMatricola(matricola);
        a.setRuolo(ruolo);
        a.setDipartimento(dip);
        a.setAttivato(true); // Default attivi per test

        em.persist(a);
        return a;
    }
}