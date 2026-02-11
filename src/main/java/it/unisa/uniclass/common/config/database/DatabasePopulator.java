package it.unisa.uniclass.common.config.database;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.model.Aula;
import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Giorno;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Tipo;

import jakarta.annotation.PostConstruct;
import jakarta.ejb.Singleton;
import jakarta.ejb.Startup;
import jakarta.persistence.EntityManager;
import jakarta.persistence.PersistenceContext;

import java.sql.Time; // Fondamentale per i campi orario di Lezione
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

        System.out.println("=== POPOLAMENTO DB AVVIATO ===");

        // ---------------------------
        // 0. ANNO DIDATTICO
        // ---------------------------
        AnnoDidattico annoCorrente = new AnnoDidattico("2024/2025");
        em.persist(annoCorrente);

        // ---------------------------
        // 1. CORSO DI LAUREA
        // ---------------------------
        CorsoLaurea cl = new CorsoLaurea("Informatica");

        // Collega l'anno al corso di laurea (popola la join table corso_laurea_anno_didattico)
        List<AnnoDidattico> anni = new ArrayList<>();
        anni.add(annoCorrente);
        cl.setAnniDidattici(anni);

        List<CorsoLaurea> corsi = new ArrayList<>(); corsi.add(cl); annoCorrente.setCorsiLaurea(corsi); // Persisti entrambi
        em.persist(cl);
        em.persist(annoCorrente);


        // ---------------------------
        // 2. DOCENTE
        // ---------------------------
        Accademico docente = new Accademico();
        docente.setEmail("docente.test@unisa.it");
        docente.setPassword("Test123%");
        docente.setNome("Mario");
        docente.setCognome("Rossi");
        docente.setDataNascita(LocalDate.of(1980, 1, 1));
        docente.setTelefono("3331112222");
        docente.setIscrizione(LocalDate.now());
        docente.setTipo(Tipo.Accademico);
        docente.setMatricola("D0001");
        docente.setRuolo(Ruolo.DOCENTE);
        docente.setDipartimento("Informatica");
        docente.setAttivato(true);
        em.persist(docente);

        // ---------------------------
        // 3. STUDENTE
        // ---------------------------
        Accademico studente = new Accademico();
        studente.setEmail("studente.test@unisa.it");
        studente.setPassword("Test123%");
        studente.setNome("Luca");
        studente.setCognome("Bianchi");
        studente.setDataNascita(LocalDate.of(2000, 1, 1));
        studente.setTelefono("3334445555");
        studente.setIscrizione(LocalDate.now());
        studente.setTipo(Tipo.Accademico);
        studente.setMatricola("S0001");
        studente.setRuolo(Ruolo.STUDENTE);
        studente.setDipartimento("Informatica");
        studente.setAttivato(true);
        studente.setCorsoLaurea(cl);
        em.persist(studente);

        // ---------------------------
        // 4. CORSI
        // ---------------------------
        Corso c1 = new Corso("Programmazione 1");
        c1.setCorsoLaurea(cl);
        c1.setAnnoDidattico(annoCorrente);
        em.persist(c1);

        Corso c2 = new Corso("Basi di Dati");
        c2.setCorsoLaurea(cl);
        c2.setAnnoDidattico(annoCorrente);
        em.persist(c2);

        Corso c3 = new Corso("Algoritmi");
        c3.setCorsoLaurea(cl);
        c3.setAnnoDidattico(annoCorrente);
        em.persist(c3);

        // ---------------------------
        // 5. RESTI
        // ---------------------------
        Resto r1 = new Resto("Resto 1", cl);
        em.persist(r1);

        Resto r2 = new Resto("Resto 2", cl);
        em.persist(r2);

        // ---------------------------
        // 6. AULE
        // ---------------------------
        // Nota: in base al tuo model Aula.java, usiamo solo nome ed edificio.
        Aula a1 = new Aula();
        a1.setNome("Aula F1");
        a1.setEdificio("Edificio F3");
        em.persist(a1);

        Aula a2 = new Aula();
        a2.setNome("Aula P1");
        a2.setEdificio("Edificio F2");
        em.persist(a2);

        // ---------------------------
        // 7. LEZIONI
        // ---------------------------

        // Lezione 1: Programmazione 1 - Lunedì 09:00-11:00 - Semestre 1 - Resto 1
        Lezione l1 = new Lezione();
        l1.setGiorno(Giorno.LUNEDI);
        // Usa java.sql.Time per rispettare il tipo nel model Lezione
        l1.setOraInizio(Time.valueOf("09:00:00"));
        l1.setOraFine(Time.valueOf("11:00:00"));
        l1.setSemestre(1); // Usa int
        l1.setAula(a1);
        l1.setCorso(c1);
        l1.setResto(r1);
        em.persist(l1);

        // Lezione 2: Basi di Dati - Martedì 11:00-13:00 - Semestre 1 - Resto 1
        Lezione l2 = new Lezione();
        l2.setGiorno(Giorno.MARTEDI);
        l2.setOraInizio(Time.valueOf("11:00:00"));
        l2.setOraFine(Time.valueOf("13:00:00"));
        l2.setSemestre(1);
        l2.setAula(a1);
        l2.setCorso(c2);
        l2.setResto(r1);
        em.persist(l2);

        // Lezione 3: Algoritmi - Mercoledì 14:00-16:00 - Semestre 1 - Resto 2
        Lezione l3 = new Lezione();
        l3.setGiorno(Giorno.MERCOLEDI);
        l3.setOraInizio(Time.valueOf("14:00:00"));
        l3.setOraFine(Time.valueOf("16:00:00"));
        l3.setSemestre(1);
        l3.setAula(a2);
        l3.setCorso(c3);
        l3.setResto(r2);
        em.persist(l3);

        System.out.println("=== POPOLAMENTO DB COMPLETATO ===");
    }
}